/*****************************************************************************
****
****    Topic: Project ECE650
**** 
*****************************************************************************/

/*****************************************************************************
****
****    Reference: geeksforgeeks.org
****               https://stackoverflow.com/
****
*****************************************************************************/

/*****************************************************************************
****
****    Import Library
****
*****************************************************************************/

#include <iostream>
#include <sstream>
#include <fstream> 
#include <string>
#include <limits>
#include <regex>
#include <vector>
#include <list>
#include <algorithm>
#include <climits>
// defined std::unique_ptr
#include <memory>
// defines Var and Lit
#include "minisat/core/SolverTypes.h"
// defines Solver
#include "minisat/core/Solver.h"
#include <thread>
#include <pthread.h>
#include <chrono>
#include <time.h>

using namespace std;

#define TIMEOUT 300
/*#define PRINT_TIME_TAKEN 1*/
string ERROR = "Error: ";
int src = -1;
int dest = -1;

class Graph {
    int vertices;
    vector<int> *adjList;
    vector<int> *adjList_VC1;
    vector<int> *adjList_VC2;
public:
    string ret_from_CNF_SAT_Minimum_VC_TH;
    string ret_from_ApproxVC_1;
    string ret_from_ApproxVC_2;
    bool minimum_vertex_cover;
    Graph(int vertices);
    void add_edge(int src, int dest);
    void Minimum_VertexCover();
    void init_Reduction_Matrix(int no_of_vertices, int k, 
        Minisat::Solver &solver, 
        vector<std::vector<Minisat::Lit>>& reduction_matrix);
    void reduction_1(int no_of_vertices, int k,
        Minisat::Solver &solver, 
        vector<std::vector<Minisat::Lit>>& reduction_matrix);
    void reduction_2(int no_of_vertices, int k,
        Minisat::Solver &solver, 
        vector<std::vector<Minisat::Lit>>& reduction_matrix);
    void reduction_3(int no_of_vertices, int k,
        Minisat::Solver &solver, 
        vector<std::vector<Minisat::Lit>>& reduction_matrix);
    void reduction_4(int no_of_vertices, int k,
        Minisat::Solver &solver, 
        vector<std::vector<Minisat::Lit>>& reduction_matrix);
    void ApproxVC_1();
    void ApproxVC_2();
    int find_highest_degree();
    void pick_edge(pair<int, int> &edge);
};

class timer {
public:
    std::chrono::time_point<std::chrono::high_resolution_clock> lastTime;
    timer() : lastTime(std::chrono::high_resolution_clock::now()) {}
    inline double elapsed() {
        std::chrono::time_point<std::chrono::high_resolution_clock> thisTime=std::chrono::high_resolution_clock::now();
        double deltaTime = std::chrono::duration<double>(thisTime-lastTime).count();
        lastTime = thisTime;
        return deltaTime;
    }
};

enum threads{
CNF_SAT_ENUM,
APPROX_VC1_ENUM,
APPROX_VC2_ENUM
};

time_t time_exec_in_sec[3];
long time_exec_in_ns[3];
bool is_time_available[3];

Graph* g = new Graph(0);

Graph::Graph(int v) {
    this->vertices = v;
    adjList = new vector<int>[v];
    adjList_VC1 = new vector<int>[v];
    adjList_VC2 = new vector<int>[v];
}

// utility function to form edge between two vertices
// source and dest
void Graph::add_edge(int src, int dest)
{
    adjList[src].push_back(dest);
    adjList[dest].push_back(src);
    adjList_VC1[src].push_back(dest);
    adjList_VC1[dest].push_back(src);
    adjList_VC2[src].push_back(dest);
    adjList_VC2[dest].push_back(src);
}

string ltrim(const string &s) {
    return regex_replace(s, regex("^\\s+"), string(""));
}
 
string rtrim(const string &s) {
    return regex_replace(s, regex("\\s+$"), string(""));
}
 
string trim(const string &s) {
    return ltrim(rtrim(s));
}

bool edge_parser(Graph *g, string edge_str, int vertices){
    pair<int, int> edge;
    if ((edge_str[0] != '{') || (edge_str[edge_str.length()-1] != '}'))
        return false;
    edge_str.erase(0, 1);
    edge_str[edge_str.length()-1] = ',';
    try {
        sregex_iterator end;
        regex pair_num("^<[0-9]+,[0-9]+>,");
        string::iterator begin_index = edge_str.begin();
        while(begin_index != edge_str.end()){
            sregex_iterator next_pair(begin_index, edge_str.end(), pair_num);
            if(next_pair != end){
                smatch pair_match;
                pair_match = *next_pair;
                string pair_str = pair_match.str();
                begin_index += pair_match.length();
                pair_str.erase(0, 1);
                pair_str.erase(pair_str.length()-2);
                edge.first = stoi(pair_str.substr(0, pair_str.find(',')));
                edge.second = stoi(pair_str.substr(pair_str.find(',')+1, pair_str.length()));
                if(edge.first > vertices || edge.second > vertices ||
                   edge.first < 1 || edge.second < 1 || edge.first == edge.second)
                   return false;
                g->add_edge(edge.first-1, edge.second-1);
            }
            else{
                return false;
            }
        }   
    }
    catch(const char* message){
        cout << "Error: Fatal";
        return false;
    }
    return true;
}


static void pclock(threads from_thread)
{
    struct timespec ts1;
    if (clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts1) == -1)
        std::cout << "Error: Failed to initialise the timer for pclock: " << errno << endl;
    time_exec_in_sec[from_thread] = ts1.tv_sec;
    time_exec_in_ns[from_thread] =  ts1.tv_nsec/1000;
}

void Graph::init_Reduction_Matrix(int no_of_vertices, int k, 
Minisat::Solver &solver, vector<std::vector<Minisat::Lit>>& reduction_matrix){
    for(int i = 0; i < no_of_vertices; i++){
        for(int j = 0; j < k; j++){
            Minisat::Lit literal = Minisat::mkLit(solver.newVar());
            reduction_matrix[i].push_back(literal);
        }
    }
}

void Graph::reduction_1(int no_of_vertices, int k, 
Minisat::Solver &solver, vector<std::vector<Minisat::Lit>>& reduction_matrix){
    for (unsigned int i = 0; i < k; i++) {
        Minisat::vec<Minisat::Lit> literal;
        for (unsigned int j = 0; j < no_of_vertices; j++) {
            literal.push(reduction_matrix[j][i]);
        }
        solver.addClause(literal);
    }
}

void Graph::reduction_2(int no_of_vertices, int k, 
Minisat::Solver &solver, vector<std::vector<Minisat::Lit>>& reduction_matrix){
    for (unsigned int m = 0; m < no_of_vertices; m++){
        for (unsigned int p = 0; p < k; p++){
            for (unsigned int q = p + 1; q < k; q++) {
                solver.addClause(~reduction_matrix[m][p], ~reduction_matrix[m][q]);
            }
        }
    }
}

void Graph::reduction_3(int no_of_vertices, int k, 
Minisat::Solver &solver, vector<std::vector<Minisat::Lit>>& reduction_matrix){
    for (unsigned int m = 0; m < k; m++){
        for (unsigned int p = 0; p < no_of_vertices; p++){
            for (unsigned int q = p + 1; q < no_of_vertices; q++) {
                solver.addClause(~reduction_matrix[p][m], ~reduction_matrix[q][m]);
            }
        }
    }
}

void Graph::reduction_4(int no_of_vertices, int k, 
Minisat::Solver &solver, vector<std::vector<Minisat::Lit>>& reduction_matrix){
    for(unsigned v1 = 0 ; v1 < no_of_vertices; ++v1) {
        for (auto v2 : adjList[v1]) {
            if(v2 < v1) continue;
            Minisat::vec<Minisat::Lit> edge_lit;
            for (unsigned int w = 0; w < k; w++) {
                edge_lit.push(reduction_matrix[v1][w]);
                edge_lit.push(reduction_matrix[v2][w]);
            }
            solver.addClause(edge_lit);
        }
    }
}
void print_vector(vector<int> vect){
    for(auto i : vect){
        cout << i+1 << " ";
    }
    cout << endl;
}

void Graph::Minimum_VertexCover(){

    int no_of_vertices = vertices;
    int k = 0;
    int hi=no_of_vertices;
    int lo=1;
    k=(hi+lo)/2;
    bool res;
    std::vector<int> path;
    while (lo <= hi)
    {
        path.clear();
        Minisat::Solver solver;
        std::vector<std::vector<Minisat::Lit>> reduction_matrix(no_of_vertices);
        
        init_Reduction_Matrix(no_of_vertices, k, solver, reduction_matrix);
        reduction_1(no_of_vertices, k, solver, reduction_matrix);
        reduction_2(no_of_vertices, k, solver, reduction_matrix);
        reduction_3(no_of_vertices, k, solver, reduction_matrix);
        reduction_4(no_of_vertices, k, solver, reduction_matrix); 

        res = solver.solve();

        if(res){
            for (int i = 0; i < vertices; i++) {
                for (int j = 0; j < k; j++) {
                    if (Minisat::toInt(solver.modelValue(reduction_matrix[i][j])) == 0) {
                        path.push_back(i);
                    }
                }
            }
            std::sort(path.begin(), path.end());
            ret_from_CNF_SAT_Minimum_VC_TH.clear();
            ret_from_CNF_SAT_Minimum_VC_TH = "CNF-SAT-VC: ";
            for (unsigned j=0; j < path.size(); j++){
                ret_from_CNF_SAT_Minimum_VC_TH += to_string(path[j]+1);
                ret_from_CNF_SAT_Minimum_VC_TH += ",";
            }
            ret_from_CNF_SAT_Minimum_VC_TH.erase(ret_from_CNF_SAT_Minimum_VC_TH.end()-1); 
            hi=k-1;
        }
        else {
            lo=k+1;
        }
        k=(lo+hi)/2;
    }
               
}

int Graph::find_highest_degree(){
    int max = 0;
    int ret_val = -1;
    for(unsigned i = 0 ; i < vertices; ++i) {
        if(adjList_VC1[i].size() > max){
            max = adjList_VC1[i].size();
            ret_val = i;
        }
    }
    return ret_val;
}

void Graph::ApproxVC_1(){
    //find_highest_weight()
    timer stopwatch;
    std::vector<int> path;
    while(true){
        int index = find_highest_degree();
        if(index == -1){
            // cout << "Error: From find_highest_degree()";
            break;
        }
        // cout << "Delete index " << index << ": ";
        // print_vector(adjList_VC1[index]);
        for (auto i : adjList_VC1[index]) {
            int remove_index = i;
            // cout << "Remove" << index << " ";
            // print_vector(adjList_VC1[remove_index]);
            adjList_VC1[remove_index].erase(
                remove(adjList_VC1[remove_index].begin(), 
                adjList_VC1[remove_index].end(), index));
            // print_vector(adjList_VC1[remove_index]);
        }
        adjList_VC1[index].clear();
        path.push_back(index);
        // print_vector(adjList_VC1[index]);
    }
    std::sort(path.begin(), path.end());
    ret_from_ApproxVC_1.clear();
    ret_from_ApproxVC_1 = "APPROX-VC-1: ";
    for (unsigned j=0; j < path.size(); j++){
        ret_from_ApproxVC_1 += to_string(path[j]+1);
        ret_from_ApproxVC_1 += ",";
    }
    ret_from_ApproxVC_1.erase(ret_from_ApproxVC_1.end()-1);
    //cout << out << endl;
    // timer_ApproxVC_1 = stopwatch.elapsed();
}

void Graph::pick_edge(pair<int, int> &edge){
    edge.first = -1;
    edge.second = -1;
    for(unsigned i = 0 ; i < vertices; ++i) {
        // cout << adjList_VC2[i].size() << " " << endl;
        if(adjList_VC2[i].size() > 0){
            edge.first = i;
            edge.second = adjList_VC2[i][0];
            break;
        }
    }
}

void Graph::ApproxVC_2(){
    timer stopwatch;
    std::vector<int> path;    
    while(true){
        pair<int, int> edge;
        pick_edge(edge);
        // cout << edge.first << " " << edge.second << endl;
        if(edge.first == -1){
            break;
        }
        // cout << "start:" << edge.first << " " << edge.second <<endl;
        // for(unsigned v1 = 0 ; v1 < vertices; ++v1) {
        //     cout << v1 << ": ";
        //     print_vector(adjList_VC2[v1]);
        // }
        for (auto i : adjList_VC2[edge.first]) {
            int remove_index = i;
            // cout << "Remove" << index << " ";
            // print_vector(adjList_VC2[remove_index]);
            adjList_VC2[remove_index].erase(
                remove(adjList_VC2[remove_index].begin(), 
                adjList_VC2[remove_index].end(), edge.first));
            // print_vector(adjList_VC2[remove_index]);
        }
        adjList_VC2[edge.first].clear();


        for (auto i : adjList_VC2[edge.second]) {
            int remove_index = i;
            // cout << "Remove" << index << " ";
            // print_vector(adjList_VC2[remove_index]);
            adjList_VC2[remove_index].erase(
                remove(adjList_VC2[remove_index].begin(), 
                adjList_VC2[remove_index].end(), edge.second));
            // print_vector(adjList_VC2[remove_index]);
        }
        adjList_VC2[edge.second].clear();

        path.push_back(edge.first);
        path.push_back(edge.second);
        // cout << "end"<<endl;
        // for(unsigned v1 = 0 ; v1 < vertices; ++v1) {
        //     cout << v1 << ": ";
        //     print_vector(adjList_VC2[v1]);
        // }
        // timer_ApproxVC_1 = stopwatch.elapsed();
    }

    std::sort(path.begin(), path.end());
    ret_from_ApproxVC_2.clear();
    ret_from_ApproxVC_2 = "APPROX-VC-2: ";
    for (unsigned j=0; j < path.size(); j++){
        ret_from_ApproxVC_2 += to_string(path[j]+1);
        ret_from_ApproxVC_2 += ",";
    }
    ret_from_ApproxVC_2.erase(ret_from_ApproxVC_2.end()-1);
    //cout << out << endl;
}

void thread_handle(int error, int type){
    string methods[3] = {"CNFSAT", "Approx_VC1", "Approx_VC2"};
    if (error)
    {
        std::cout << methods[type] << "Thread creation failed : " << strerror(error);
    }
}

void* thread2CNFSAT(void* arg) {
    is_time_available[CNF_SAT_ENUM] = 0;
    g->Minimum_VertexCover();
    pclock(CNF_SAT_ENUM);
    is_time_available[CNF_SAT_ENUM] = 1;  
    return (void*)0; 
}

void* thread2ApproxVC1(void* arg) {
    is_time_available[APPROX_VC1_ENUM] = 0;
    g->ApproxVC_1();
    pclock(APPROX_VC1_ENUM);
    is_time_available[APPROX_VC1_ENUM] = 1; 
    return (void*)0; 
}

void* thread2ApproxVC2(void* arg) {
    is_time_available[APPROX_VC2_ENUM] = 0;
    g->ApproxVC_2();
    pclock(APPROX_VC2_ENUM);
    is_time_available[APPROX_VC2_ENUM] = 1; 
    return (void*)0; 
}


int main()
{
    string cmd;
    sregex_iterator end;
    int v = 0;
    pthread_t CNF_SAT_Minimum_VC_TH, ApproxVC_1_TH, ApproxVC_2_TH;
    while(getline(cin, cmd)){
        cmd = trim(cmd);
        if (cmd.length() == 0){
            cout << ERROR <<"No command entered"<< endl;
            continue;
        }
        string st = cmd.substr(0, cmd.find(' '));
        string line = cmd.substr(cmd.find(' ')+1, cmd.length());
        line = trim(line);
        char command;
        if (st.length() != 1)
            command = 'I';
        else
            command = st[0];
        if (command == 'V'){
            regex integ("^[0-9]+$");
            sregex_iterator next_integ(line.begin(), line.end(), integ);
            if(next_integ != end){
                smatch integ_match;
                integ_match = *next_integ;
                v = stoi(integ_match.str());
                if (v < 1){
                    cout << ERROR <<"Invalid 'V' command"<< " " << cmd << endl;
                }
                else{
                    src = -1;
                    dest = -1;
                    delete g;
                    g = new Graph(v);
                }
            }else{
                cout << ERROR <<"Invalid 'V' command"<< " " << cmd << endl;
            }
        }
        else if (command == 'E' && v > 0){
            if(line[0] == '{' && line[1] == '}'){
                cout << "CNF-SAT-VC: " << endl;
                cout << "APPROX-VC-1: " << endl;
                cout << "APPROX-VC-2: " << endl;
                continue;
            }
            delete g;
            g = new Graph(v);
            if(!edge_parser(g, line, v)){
                cout << ERROR << "Invalid 'E' command"<< " " << cmd << endl;
                continue;
            }

            struct timespec ts;
            if (clock_gettime(CLOCK_REALTIME, &ts) == -1) 
                std::cout << "Error: Failed to initialise the timer";
            ts.tv_sec += TIMEOUT;

            thread_handle(pthread_create(&CNF_SAT_Minimum_VC_TH, NULL, &thread2CNFSAT, NULL), 0);
            clockid_t cid_thread1;
            pthread_getcpuclockid(CNF_SAT_Minimum_VC_TH, &cid_thread1);

            thread_handle(pthread_create(&ApproxVC_1_TH, NULL, &thread2ApproxVC1, NULL), 1);
            thread_handle(pthread_create(&ApproxVC_2_TH, NULL, &thread2ApproxVC2, NULL), 2);
            
            pthread_join(ApproxVC_1_TH, NULL);
            pthread_join(ApproxVC_2_TH, NULL);

            int s = pthread_timedjoin_np(CNF_SAT_Minimum_VC_TH, NULL, &ts);
            if (s == 0) // NO error. CNF SAT executed on time
                cout << g->ret_from_CNF_SAT_Minimum_VC_TH << endl;
            else
                cout << "CNF-SAT-VC: timeout" << std::endl;
            cout << g->ret_from_ApproxVC_1 << endl;
            cout << g->ret_from_ApproxVC_2 << endl;
            #ifdef PRINT_TIME_TAKEN
                if(is_time_available[CNF_SAT_ENUM])
                    // cout << "CNF_SAT    Running time: " <<
                    // time_exec_in_sec[CNF_SAT_ENUM] << "s " << 
                    // time_exec_in_ns[CNF_SAT_ENUM] << "ms" << endl;
                    cout << time_exec_in_sec[CNF_SAT_ENUM] << ", " 
                    << time_exec_in_ns[CNF_SAT_ENUM] << ", ";
                else
                    // cout << "CNF_SAT    Running time: 5s 0ms" << endl;
                    cout << TIMEOUT << ", 0, ";

                if(is_time_available[APPROX_VC1_ENUM])
                    // cout << "ApproxVC_1 Running time: " <<
                    // time_exec_in_sec[APPROX_VC1_ENUM] << "s " << 
                    // time_exec_in_ns[APPROX_VC1_ENUM] << "ms" << endl;
                    cout << time_exec_in_sec[APPROX_VC1_ENUM] << ", " 
                    << time_exec_in_ns[APPROX_VC1_ENUM] << ", ";
                else
                    cout << "ApproxVC_1 Running time: 5s 0ms" << endl;

                if(is_time_available[APPROX_VC2_ENUM])
                    // cout << "ApproxVC_2 Running time: " <<
                    // time_exec_in_sec[APPROX_VC2_ENUM] << "s " << 
                    // time_exec_in_ns[APPROX_VC2_ENUM] << "ms" << endl;
                    cout << time_exec_in_sec[APPROX_VC2_ENUM] << ", " 
                    << time_exec_in_ns[APPROX_VC2_ENUM] << endl;
                else
                    cout << "ApproxVC_2 Running time: 5s 0ms" << endl;
            #endif
        }else
            cout << ERROR << "Invalid command. Try V->E->s"<< " " << cmd << endl;
    }
    return 0;
}
