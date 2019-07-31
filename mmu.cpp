#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <iomanip>
#include <limits>
#include <algorithm>
#include <cstring>
#include <bits/stdc++.h>
#include <map>

using namespace std;


// Global variables

static ifstream file;
FILE *inputFile;
int PT_SIZE = 64;
int frame_amount;
int DEFAULT_FRAME_AMOUNT = 16;
int inst_count = 0;
int ctx_switches = 0;
int process_exits = 0;
int last_victim_index = -1;
int timer;
static int used_random_index = 0; // count the index of random number which was already used
bool p_cmt = false;
bool begin_select_victim = false;
bool SEGV;
bool first_w = true;
bool print_O = false;
string pager_type;
vector<pair<string,string>> instructions;
vector<int> random_num_vector;


// Structs

typedef struct {    //can only be total of 32-bit size
    unsigned valid:1;
    unsigned write_protect:1;
    unsigned modified:1;
    unsigned pre_modified:1;
    unsigned referenced:1;
    unsigned pre_referenced:1;
    unsigned pagedout:1;
    unsigned file_map:1;
    unsigned second_chance:1;
    unsigned frame_index:8;
    unsigned proc_id:7;
    unsigned page_index:8;
} pte_t;


typedef struct {     //for reverese mapping from frame to PTE
    int proc_id;
    int vpage;
    int frame_index;
    bool used = false;
    unsigned age_bit:32;
} frame_t;


typedef struct {    //counting info for per process
    int proc_id;
    int unmaps = 0;
    int maps = 0;
    int ins = 0;
    int outs = 0;
    int fins = 0;
    int fouts = 0;
    int zeros = 0;
    int segv = 0;
    int segprot = 0;
} pstats;


typedef struct {
    int cl;
    unsigned int last_use_time;
    unsigned int age;
} info_usage;


// Global Instances

vector<pstats*> pstats_table;
vector<frame_t*> free_frame_list;
vector<frame_t*> using_frame_list;
vector<frame_t*> frame_table;


// Classes

class Process {
    public:
        int pid;
        vector<vector<int>> vma;
        vector<pte_t*> page_table;
        vector<info_usage*> iu_table;

        Process() {}    //constructor

        void init(int p) {
            pid = p;

            for (int i = 0; i < PT_SIZE; i++) {
                pte_t* pte = new pte_t();
                info_usage* iu = new info_usage();

                pte->valid = false;
                pte->write_protect = false;
                pte->modified = false;
                pte->pre_modified = false;
                pte->referenced = false;
                pte->pre_referenced = false;
                pte->pagedout = false;
                pte->file_map = false;
                pte->frame_index = 0;
                pte->proc_id = pid;
                pte->page_index = i;
                pte->second_chance = true;
                page_table.push_back(pte);

                iu->last_use_time = 0;
                iu->age = 0;
                iu_table.push_back(iu);

                //this part is for printing statistic result usage
                pstats* p_stats = new pstats();
                p_stats->proc_id = pid;
                pstats_table.push_back(p_stats);
            }
        }
};


// Global Instances

vector<Process*> process;


pte_t* frame_to_page(frame_t* frame) {
    Process* p = process[frame->proc_id];
    pte_t* pte = p->page_table[frame->vpage];
    return pte;
}


int myrandom(int frame_amount) {
    used_random_index++;
    // reset index if already been to the end of the vector
    if (used_random_index == random_num_vector.size()) used_random_index = 1;
    return 0 + (random_num_vector[used_random_index] % frame_amount);
}


class Pager {
    public:
        virtual frame_t* select_victim_frame(pte_t* pte_new) = 0;     //this funciton will return a victim frame
};


class FIFO : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {
            frame_t* frame = using_frame_list.front();
            using_frame_list.erase(using_frame_list.begin());

            return frame;
        }
};


class Random : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {
            int frame_idx = myrandom(frame_amount);

            frame_t* frame = using_frame_list[frame_idx];
            using_frame_list.erase(using_frame_list.begin() + frame_idx);

            return frame;
        }
};


class Clock : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {
            frame_t* frame = using_frame_list.front();
            pte_t* pte = frame_to_page(frame);

            while (pte->second_chance) {
                pte->second_chance = false;
                pte->pre_referenced = pte->referenced;
                pte->referenced = false;

                using_frame_list.erase(using_frame_list.begin());
                using_frame_list.push_back(frame);

                frame = using_frame_list.front();
                pte = frame_to_page(frame);
            }

            using_frame_list.erase(using_frame_list.begin());
            return frame;
        }
};


void update_class(pte_t* pte) {
    if (!pte->referenced && !pte->modified) { process[pte->proc_id]->iu_table[pte->page_index]->cl = 0; }
    else if (!pte->referenced && pte->modified) { process[pte->proc_id]->iu_table[pte->page_index]->cl = 1; }
    else if (pte->referenced && !pte->modified) { process[pte->proc_id]->iu_table[pte->page_index]->cl = 2; }
    else { process[pte->proc_id]->iu_table[pte->page_index]->cl = 3; }
}


pte_t* compare_cur_lowest_class(pte_t* pte, pte_t* next_victim) {
    //compare current lowest class of all the pages in memory
    if (process[pte->proc_id]->iu_table[pte->page_index]->cl < process[next_victim->proc_id]->iu_table[next_victim->page_index]->cl) {
        next_victim = pte;
    }
    return next_victim;
}


pte_t* compare_cur_lowest_age_bit(pte_t* pte, pte_t* next_victim) {
    frame_t* next_victim_frame = using_frame_list[next_victim->frame_index];
    frame_t* frame = using_frame_list[pte->frame_index];

    //compare current lowest age bit
    if (frame->age_bit < next_victim_frame->age_bit) {
        next_victim_frame = frame;
        next_victim = pte;
    }

    return next_victim;
}


pte_t* compare_cur_highest_age(pte_t* pte, pte_t* next_victim) {
    if (pte->referenced) {
        pte->referenced = false;
        process[pte->proc_id]->iu_table[pte->page_index]->last_use_time = inst_count - 1;
        process[pte->proc_id]->iu_table[pte->page_index]->age = (inst_count - 1) - process[pte->proc_id]->iu_table[pte->page_index]->last_use_time;
    }

    //compare current highest age of all the pages in memory
    if (process[pte->proc_id]->iu_table[pte->page_index]->age > process[next_victim->proc_id]->iu_table[next_victim->page_index]->age) {
        next_victim = pte;
    }

    return next_victim;
}


void aging_action() {
    for (int i = 0; i < using_frame_list.size(); i++) {
        if (frame_to_page(using_frame_list[i])->referenced) {
            unsigned int tmp = 1;
            tmp = tmp << 31;
            using_frame_list[i]->age_bit = (using_frame_list[i]->age_bit | tmp);
        }

        frame_to_page(using_frame_list[i])->referenced = false;
    }
}


frame_t* time_out_style_algo() {
    int cur_index = last_victim_index + 1;  //strat from the next position since last victim was picked out
    frame_t* frame = using_frame_list[cur_index];
    pte_t* next_victim = frame_to_page(frame);

    int begin_page = next_victim->page_index;
    int begin_proc = next_victim->proc_id;
    pte_t* pte = frame_to_page(frame);
    bool find_fifty_case = false;

    for (int i = 0; i < using_frame_list.size(); i++) {
        pte_t* pte2 = frame_to_page(using_frame_list[i]);
    }

    do {
        if (pager_type == "e") { update_class(pte); }

        if (pager_type == "e") {
            next_victim = compare_cur_lowest_class(pte, next_victim);
        } else if (pager_type == "a") {
            next_victim = compare_cur_lowest_age_bit(pte, next_victim);
        } else if (pager_type == "w") {
            if (process[pte->proc_id]->iu_table[pte->page_index]->age >= 50 && !pte->referenced) {
                next_victim = pte;
                break;
            }

            next_victim = compare_cur_highest_age(pte, next_victim);
        }

        if (cur_index == frame_amount - 1) { cur_index = -1; }
        cur_index++;

        frame = using_frame_list[cur_index];
        pte = frame_to_page(frame);
    } while (begin_page != pte->page_index || begin_proc != pte->proc_id);

    last_victim_index = next_victim->frame_index;
    if (last_victim_index == frame_amount - 1) { last_victim_index = -1; }  //go back to the head if facing tail

    if (pager_type == "w" && first_w) {
        for (int i = 0; i < using_frame_list.size(); i++) {
            pte_t* pte3 = frame_to_page(using_frame_list[i]);
            if (pte3->referenced) {
                pte3->referenced = false;
                process[pte3->proc_id]->iu_table[pte3->page_index]->last_use_time = inst_count - 1;
            }
        }

        first_w = false;
    }

    if (pager_type == "a") {
        for (int i = 0; i < using_frame_list.size(); i++) {
            //shift the age_bit after the compare_cur_lowest_age_bit !
            using_frame_list[i]->age_bit = using_frame_list[i]->age_bit >> 1;
        }
    }

    frame_t* frame_new = using_frame_list[next_victim->frame_index];
    using_frame_list.erase(using_frame_list.begin() + next_victim->frame_index);

    return frame_new;
}


void reset_ref_bit() {
    for (int i = 0; i < using_frame_list.size(); i++) {
        pte_t* pte = frame_to_page(using_frame_list[i]);
        pte->referenced = false;
    }
}


class NRU : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {
            frame_t* frame = time_out_style_algo();

            if (timer >= 50 && !SEGV) {
                reset_ref_bit();
                timer = 0;
            }

            return frame;
        }
};


class Aging : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {
            return time_out_style_algo();
        }
};


class WorkingSet : public Pager {
    public:
        frame_t* select_victim_frame(pte_t* pte_new) {

            for (int i = 0; i < using_frame_list.size(); i++) {
                pte_t* pte = frame_to_page(using_frame_list[i]);

                process[pte->proc_id]->iu_table[pte->page_index]->age = (inst_count - 1) - process[pte->proc_id]->iu_table[pte->page_index]->last_use_time;
            }

            return time_out_style_algo();
        }
};


// Global Instance

Pager* the_pager;


// Functions

void create_free_frame_list (int frame_amount) {
    for (int i = 0; i < frame_amount; i++) {
        frame_t* frame = new frame_t();
        frame->frame_index = i;
        free_frame_list.push_back(frame);
        frame_table.push_back(frame);
    }
}


frame_t* allocate_frame_from_free_list() {
    frame_t *frame = free_frame_list.front();
    free_frame_list.erase(free_frame_list.begin());
    return frame;
}


void unmap(frame_t* frame) {
        Process* p = process[frame->proc_id];
        pte_t *pte = p->page_table[frame->vpage];

        if (print_O) { cout << " UNMAP " <<  frame->proc_id << ":" << frame->vpage << endl; }
        pstats_table[frame->proc_id]->unmaps += 1;

        //reset the info for unmapping
        pte->valid = false;
        pte->frame_index = 0;
        frame->proc_id = 0;
        frame->vpage = 0;
}


frame_t* get_frame(pte_t* pte_new) {
    frame_t* frame;

    if (free_frame_list.size() == 0) {
        if (pager_type == "a") { aging_action();}

        begin_select_victim = true;
        frame = the_pager->select_victim_frame(pte_new);

        Process* p = process[frame->proc_id];
        pte_t* pte_old = p->page_table[frame->vpage];
        //Once a victim frame has been determined, victim must be unmapped from its user
        unmap(frame);

        //Save frame to disk if necessary (OUT / FOUT). If the page was modified, either page out to swap device (OUT) or written back to the file (FOUT) when was file mapped
        if (pte_old->modified) {
            pte_old->pagedout = true;

            if (pte_old->file_map) {
                if (print_O) { cout << " FOUT" << endl; }
                pstats_table[pte_old->proc_id]->fouts += 1;
            }
            else {
                if (print_O) { cout << " OUT" << endl; }
                pstats_table[pte_old->proc_id]->outs += 1;
            }
        }
    }
    else {
        frame = allocate_frame_from_free_list();
        frame->used = true;
    }

    //make sure only add frame into using_frame_list when it is not yet in using_frame_list
    bool check_exist = false;
    for (int i = 0; i < using_frame_list.size(); i++) {
        if (frame->frame_index == using_frame_list[i]->frame_index) {
            check_exist = true;
        }
    }

    if (!check_exist) {
        if (pager_type == "r" || pager_type == "e" || pager_type == "a" || pager_type == "w" ) {
            using_frame_list.insert(using_frame_list.begin() + frame->frame_index, frame);
        }
        else {
            using_frame_list.push_back(frame);
        }
    }

    return frame;
}


void page_fault_handler(Process* current_process, int vpage, string inst_type) {
    int start_vpage;
    int end_vpage;
    SEGV = true;

    pte_t* pte = current_process->page_table[vpage];

    //determine the vpage can be accessed (it's part of VMAs or not)
    for (int i = 0; i < current_process->vma.size(); i++) {
        start_vpage = current_process->vma[i][0];
        end_vpage = current_process->vma[i][1];

        if (vpage >= start_vpage && vpage <= end_vpage) {
            SEGV = false;

            //On the first page fault, have to search for the vaddr in the VMA list, and assign File or WriteProtect bits
            pte->write_protect = current_process->vma[i][2];
            pte->file_map = current_process->vma[i][3];

            break;
        }
    }

    if (SEGV) {     //if not, create a SEGV output
        if (print_O) { cout << " SEGV" << endl; }
        pstats_table[pte->proc_id]->segv += 1;
        return;
    }

    //if yes, a frame must be allocated, assigned to the PTE belonging to the vpage of this inst
    frame_t *newframe = get_frame(pte);

    //then populated with proper content depends on whether this page was previously page out (IN, FIN,ZERO)
    if (pte->file_map) {    //do FIN when is a memory mapped file
            if (print_O) { cout << " FIN" << endl; }
            pstats_table[pte->proc_id]->fins += 1;
    }

    if (pte->pagedout && !pte->file_map) {      //do IN when the page is from swap space
        if (print_O) { cout << " IN" << endl; }
        pstats_table[pte->proc_id]->ins += 1;
    }

    if (!pte->pagedout && !pte->file_map) {//if vpage was never swapped out and is not file mappped, issue Zero output
        if (print_O) { cout << " ZERO" << endl; }
        pstats_table[pte->proc_id]->zeros += 1;
    }

    //Map the frame with new page
    pte->frame_index = newframe->frame_index;
    newframe->proc_id = current_process->pid;
    newframe->vpage = vpage;
    if (print_O) { cout << " MAP " << dec << newframe->frame_index << endl; }
    pstats_table[pte->proc_id]->maps += 1;

    //Since this page is swap in, and not need the folowing states anymore, so just reset it
    pte->modified = false;
    //in Working Set case, need to maintain previous R bit if facing "Stop" case
    pte->referenced = false;
    pte->second_chance = true;  //a new coming page must enable with second chance
    pte->valid = true;      //Under what condition that need to set valid bit to false
    process[pte->proc_id]->iu_table[pte->page_index]->last_use_time = inst_count - 1;

    if (pager_type == "a") {
        newframe->age_bit = 1;
        newframe->age_bit = newframe->age_bit << 31;
    }
}


void update_pte(pte_t* pte, string inst_type) {
    if (inst_type == "w") {
        //if there's SEGPROT, then no need to update modified bit, which means the write is failed
        if (!pte->write_protect) {pte->modified = true;}
        pte->referenced = true;
    } else if (inst_type == "r") {
        pte->referenced = true;
    }
}


void Simulator() {
    string inst_type;
    string inst_val;
    int proc_id;
    int vpage;
    Process* current_process;
    timer = 0;

    for (int i = 0; i < instructions.size(); i++) {
        inst_type = instructions[i].first;
        inst_val = instructions[i].second;

        inst_count += 1;
        timer += 1;
        if (print_O) { cout << dec << i << ": ==> " << inst_type << " " << inst_val << endl; }

        //handle special case of "c" and "e" instruction
        if (inst_type == "c") {
            proc_id = stoi(inst_val);
            current_process = process[proc_id];
            ctx_switches += 1;
        }
        else if (inst_type == "e") {
            proc_id = stoi(inst_val);
            if (print_O) { cout << "EXIT current process " << proc_id << endl; }

            for (int i = 0; i < current_process->page_table.size(); i++) {
                pte_t* pte = current_process->page_table[i];

                if (pte->valid) {
                    //reverse mapping from page to frame
                    frame_t* frame = frame_table[pte->frame_index];
                    unmap(frame);

                    free_frame_list.push_back(frame);

                    //when exit, if any modified PTE, only need to written back to the file (FOUT), no need to handle out to swap area case
                    if (pte->modified && pte->file_map) {
                        pte->pagedout = true;

                        if (print_O) { cout << " FOUT" << endl; }
                        pstats_table[pte->proc_id]->fouts += 1;
                    }
                }
                pte->pagedout = false;  //when exit a process, set all the page's pagedout bit to false
            }
            process_exits += 1;
        }
        //now the real instructions for read and write
        else {
            vpage = stoi(inst_val);
            pte_t *pte = current_process->page_table[vpage];

            if (!pte->valid) {    //this case will generate the page fault
                page_fault_handler(current_process, vpage, inst_type);
            }
            else {
                //some algos have to maintain the page's original status when this required page already exist in memory
                if (pte->pre_referenced) { pte->referenced = pte->pre_referenced; }
                if (pte->pre_modified) { pte->modified = pte->pre_modified; }
                pte->second_chance = true;  //eanble second_chance if the new required page still exist in memory
            }

            if (pte->write_protect && inst_type == "w") {
                if (print_O) { cout << " SEGPROT" << endl; }
                pte->referenced = true;
                pstats_table[pte->proc_id]->segprot += 1;
            }

            //Mark reference/modified bit as indicated by inst. (simulate inst. execution by hw)
            update_pte(pte, inst_type);    //read/modify/write bits based on operations
        }
    }
}


void read_file(char * filename) {
    ifstream inFile (filename);
    string line;
    string word;
    string inst_type;
    string inst_val;
    int pro_amount;
    int vma_amount;
    int proc_count = 0;
    bool inst_simulator = false;
    bool pro_amount_flag = true;
    pair<string, string> pair;

    while(getline(inFile, line)) {
        stringstream ls(line);

        while(ls >> word) {
            //if the first string in a line is #, jump to the next line
            if (word == "#") { break; }

            //if the first char of the first stirng in a line is #
            char word_char[word.length() + 1];
            strcpy(word_char, word.c_str());
            if (word_char[0] == '#') { break; }

            if (word == "c") { inst_simulator = true;}

            if (!inst_simulator) {
                if  (pro_amount_flag) {    //get the total process amount
                    pro_amount = stoi(word);
                    pro_amount_flag = false;
                    continue;
                }

                //create new process and store in process vector
                Process* proc = new Process();
                proc->init(proc_count);
                process.push_back(proc);
                proc_count++;

                vma_amount = stoi(word);     //get process's VMAs amount

                for (int i = 0; i < vma_amount; i++) {
                    getline(inFile, line);
                    stringstream ls(line);

                    //attach VMAs info into each process
                    vector<int> vma;
                    proc->vma.push_back(vma);
                    for (int j = 0; j < 4; j++) {
                        ls >> word;
                        proc->vma[i].push_back(stoi(word));
                    }
                }
            }
            else {
                inst_type = word;
                ls >> word;
                inst_val = word;

                pair = make_pair(inst_type, inst_val);
                instructions.push_back(pair);
            }
        }
    }
}


void read_randoms(string rand_file) {
    file.open(rand_file);
    string random_item;

    while(file >> random_item) { // read and store all the random numbers into random_num_vector vector
        random_num_vector.push_back(stoi(random_item));
    }
    file.close();
}


void PrintResult(bool print_P, bool print_F, bool print_S){
    if(print_P) {
        for (int i = 0; i < process.size(); i++) {
            printf("PT[%d]: ", process[i]->pid);

            for (int j = 0; j < process[i]->page_table.size(); j++) {
                pte_t* pte = process[i]->page_table[j];

                if (!pte->valid) {
                    if(pte->pagedout && !pte->file_map) {
                        printf("#");
                    }
                    else {printf("*");}
                }
                else {
                    printf("%d:", pte->page_index);

                    if (pte->referenced) {printf("R");} else {printf("-");}
                    if (pte->modified) {printf("M");} else {printf("-");}
                    //has been swapped out and associated with swap area
                    if (pte->pagedout && !pte->file_map) {printf("S");} else {printf("-");}
                }
                printf(" ");
            }
            printf("\n");
        }
    }

    if (print_F) {
        printf("FT:");
        for (int i = 0; i < frame_table.size(); i++) {
            printf(" ");

            if (frame_table[i]->used) {
                printf("%d:%d", frame_table[i]->proc_id,frame_table[i]->vpage);
            }
            else {
                printf("*");
            }
        }
        printf("\n");
    }

    if (print_S) {
        unsigned long long cost = 0;
        for (int i = 0; i < process.size(); i++) {
            printf("PROC[%d]: U=%lu M=%lu I=%lu O=%lu FI=%lu FO=%lu Z=%lu SV=%lu SP=%lu\n",
                process[i]->pid,
                pstats_table[i]->unmaps,
                pstats_table[i]->maps,
                pstats_table[i]->ins,
                pstats_table[i]->outs,
                pstats_table[i]->fins,
                pstats_table[i]->fouts,
                pstats_table[i]->zeros,
                pstats_table[i]->segv,
                pstats_table[i]->segprot);

            cost +=  (pstats_table[i]->unmaps + pstats_table[i]->maps) * 400 +
                    (pstats_table[i]->ins + pstats_table[i]->outs) * 3000 +
                    (pstats_table[i]->fins + pstats_table[i]->fouts) * 2500 +
                    (pstats_table[i]->zeros) * 150 +
                    pstats_table[i]->segv * 240 +
                    pstats_table[i]->segprot * 300;
        }

        cost += (inst_count - ctx_switches - process_exits) * 1 +
                ctx_switches * 121 +
                process_exits * 175;

        printf("TOTALCOST %lu %lu %lu %lu\n", inst_count, ctx_switches, process_exits, cost);
    }
}


int main(int argc, char* argv[]) {
    int i = 1;
    bool print_P = false;
    bool print_F = false;
    bool print_S = false;
    string frame_amt = "0";

    for (int j = 0; j < 3; j++) {
        if (argv[i][1] != 'f' && argv[i][1] == 'a' && argv[i][1] == 'o') {
            break;
        }

        if (argv[i][1] == 'f') {
            for (int j = 2; j < strlen(argv[i]); j++) {
                frame_amt += argv[i][j];
            }
        }

        //Get Commandline arguments
        if (argv[i][1] == 'a') {
            char algo = argv[i][2];

            if (argv[i][2] == 'f') {
                pager_type = "f";
                the_pager = new FIFO();
            }
            else if (argv[i][2] == 'r') {
                pager_type = "r";
                the_pager = new Random();
            }
            else if (argv[i][2] == 'c') {
                pager_type = "c";
                the_pager = new Clock();
            }
            else if (argv[i][2] == 'e') {
                pager_type = "e";
                //timeout_style = true;
                the_pager = new NRU();
            }
            else if (argv[i][2] == 'a') {
                pager_type = "a";
                //timeout_style = true;
                the_pager = new Aging();
            }
            else if (argv[i][2] == 'w') {
                pager_type = "w";
                the_pager = new WorkingSet();
            }
        }

        if (argv[i][1] == 'o') {
            string opt = argv[2];
            opt = opt.substr(2);

            for (int j = 2; j < strlen(argv[i]); j++) {
                if (argv[i][j] == 'O') {
                    print_O = true;
                }
                if (argv[i][j] == 'P') {
                    print_P = true;
                }
                if (argv[i][j] == 'F') {
                    print_F = true;
                }
                if (argv[i][j] == 'S') {
                    print_S = true;
                }
            }
        }

        i++;
    }

    frame_amount = DEFAULT_FRAME_AMOUNT;
    if (frame_amt != "0") {
        frame_amount = stoi(frame_amt);
    }
    create_free_frame_list(frame_amount);

    // Parse input file
    char* filename = argv[i];

    i++;
    string rand_file = argv[i];

    read_file(filename);
    read_randoms(rand_file);  // Init randoms

    Simulator();//Begin simulation
    PrintResult(print_P, print_F, print_S);  //Final output

    return 0;
}