#include <omp.h>
#include <time.h>
#include <iostream>
#include <random>
#include <algorithm>
#include <fstream>
#include <stdlib.h>
#include <string.h>
#include <utility>
#include <set>
#include <vector>
#include <queue>
#include <map>
#include <ctime>
#include <numeric>
#include <unordered_map>
#include <bitset>
#include <math.h>
#include "regex_to_dfa.h"
#include "Rreverse.h"


#define MAXINT ((unsigned) 4294967295)

using namespace std;

int totalV = 0, threads = 20, dis = 1, statenum = 0;
int src, dst, aplace, bplace;
int s_final = 0, mindis = 99, active_num = 0;
long long paths = 0, redpath = 0, WLTotal = 0, WLavg = 0, threshold = 100000000;
string na, name;

string charPool, regex, regex_rever;
mt19937 gen(std::random_device{}());

vector<vector<pair<int, string> > > label, rlabel; // 两者维度均为 totalV，
vector<vector<int> > pos, rpos; // 记录 SkyLineElem 不同hop下元素的数量，便于后续剪枝

vector<unordered_map<int, int> > Nlabel;

vector<vector<pair<int, char> > > con; // id + edge label

// unordered_map的key是顶点v所有对应的子路径状态
vector<unordered_map<int, vector<pair<int, char> > > > consketch;

vector<pair<int, int> > v2degree;

vector<int> visited, old2new, new2old; // DFS 访问标记

// vector<vector<unordered_map<int, long long> > > WL;
vector<unordered_map<int, unordered_map<int, long long> > > WL;


vector<vector<int> > PathSet, StateSet;



void ParaInitial(){
    label.resize(totalV),  pos.resize(totalV);
    rlabel.resize(totalV), rpos.resize(totalV);
    Nlabel.resize(totalV); visited.resize(totalV, 0);
    old2new.resize(totalV, -1), new2old.resize(totalV, -1);
}

void ParaDeletion(){
    vector<vector<pair<int, string> > >().swap(label);
    vector<vector<pair<int, string> > >().swap(rlabel);
    vector<vector<int> >().swap(pos);
    vector<vector<int> >().swap(rpos);
    vector<unordered_map<int, int> >().swap(Nlabel);
}


void GraphInitial(string filename){
    string s;
    const char *filepath = filename.c_str();
    ifstream infile;

    infile.open(filepath);
    if(!infile.is_open()){
        cout<<"No such file!"<<endl;
        exit(-1);
    }

    long xx = 0;
    // srand((unsigned)time(NULL));
    
    while(getline(infile, s)){
        char* strc = new char[strlen(s.c_str())+1];
        strcpy(strc, s.c_str());
        char* s1 = strtok(strc," ");
        
        if (xx == 0){
            totalV = atoi(s1);
            con.resize(totalV);
            consketch.resize(totalV);
            ParaInitial();
        }else{
            while(s1){
                unsigned va = xx - 1, vb = atoi(s1) - 1;
                char c = charPool[(va+vb) % charPool.size()]; 
                con[va].push_back(make_pair(vb, c));
                s1=strtok(NULL," ");
            }
        }

        xx += 1;
        
        delete s1, strc;
    }

    infile.close();

    for( int i = 0; i < totalV; ++i )
		v2degree.push_back(make_pair(con[i].size(), i));

	sort(v2degree.rbegin(), v2degree.rend());
    src = v2degree[aplace].second,  dst = v2degree[bplace].second;
    
}


void GraphTest(string filename, int kk){
    string s;
    const char *filepath = filename.c_str();
    ifstream infile;

    infile.open(filepath);
    if(!infile.is_open()){
        cout<<"No such file!"<<endl;
        exit(-1);
    }

    long xx = 0;
    // srand((unsigned)time(NULL));
    
    while(getline(infile, s)){
        char* strc = new char[strlen(s.c_str())+1];
        strcpy(strc, s.c_str());
        char* s1 = strtok(strc," ");
        
        if (xx == 0){
            totalV = atoi(s1);
            con.resize(totalV);
            consketch.resize(totalV);
            ParaInitial();
        }else {
            while(s1){
                unsigned va = xx - 1, vb = atoi(s1) - 1;
                char c = charPool[(va+vb) % charPool.size()]; 
                if((va+vb) % 10 < kk)
                    con[va].push_back(make_pair(vb, c));
                s1=strtok(NULL," ");
            }
        }

        xx += 1;
        
        delete s1, strc;
    }

    infile.close();

    for( int i = 0; i < totalV; ++i )
		v2degree.push_back(make_pair(con[i].size(), i));

	sort(v2degree.rbegin(), v2degree.rend());
    src = v2degree[aplace].second,  dst = v2degree[bplace].second;

}

void ResetLabel(vector<pair<int, string> >& labs, 
                vector<pair<int, string> >& newLab){
    
    vector<bool> bmap(statenum + 1, false);
    
    for (pair<int, string> elem : labs) bmap[elem.first] = true;
    
    int write_index = 0;
    for (pair<int, string> elem : newLab){
        if (!bmap[elem.first]) {
            // 检查是否为重复元素（与已写入的最后一个元素比较）
            if (write_index == 0 || elem.first != newLab[write_index - 1].first) {
                newLab[write_index++] = elem;
            }
        }
    }

    newLab.resize(write_index);

    vector<bool>().swap(bmap);
}

void ResetLabelhop(vector<pair<int, string> >& newLab){
    
    int write_index = 0;
    for (pair<int, string> elem : newLab){
        // 检查是否为重复元素（与已写入的最后一个元素比较）
        if ( write_index == 0 || elem.first != newLab[write_index - 1].first) {
            newLab[write_index++] = elem;
        }
    }

    newLab.resize(write_index);
}


int compute_distance(vector<pair<int, string> > lab,
                       vector<pair<int, string> > rlab,
                       RegexMatcher& matcher){
    int dis = 99;

    for (pair<int, string>& s1:lab){
        for (pair<int, string>& d1:rlab){
            string combined = s1.second + string(d1.second.rbegin(), d1.second.rend());
            auto [f1, f2] = matcher.match(combined);
            if (f1 and combined.size() < dis)
                dis = combined.size();
        }
    }

    return dis;
}


void ParallelBuild(RegexMatcher& matcher, RegexMatcher& matcher_r){
    
    omp_set_num_threads(threads);
    
    vector<int> Cnt1(totalV), Cnt2(totalV);
    vector<vector<pair<int, string> > > label_new(totalV), rlabel_new(totalV);
    
    for (int i=0; i<totalV; ++i){
        // 从src和dst开始，初始状态值设置为0
        if (i == src) { label[i].push_back(make_pair(0, "")); }
        else if (i == dst) { rlabel[i].push_back(make_pair(0, ""));}
        else { }

        pos[i].push_back( label[i].size() );
        rpos[i].push_back( rlabel[i].size() );
    } 

    for( long long cnt1 = 1, cnt2 = 1; ; ++dis ){
        cnt1 = 0, cnt2 = 0;
        
        #	pragma omp parallel
        {
            int pid = omp_get_thread_num(), np = omp_get_num_threads();
            
            for( int u = pid; u < totalV; u += np ){

                for (int i=0; i<con[u].size(); ++i){
                    
                    unsigned vid = con[u][i].first;
                    
                    char lb = con[u][i].second;

                    if (!matcher.isCharPossiblyInRegex(lb)) continue;
                    
                    if (vid != dst){
                        vector<pair<int, string> >& labs = label[vid];
                        int start = dis==1? 0:pos[vid][dis-2], end = pos[vid][dis-1];
                        
                        for (int j=start; j<end; ++j){
                            int nextstate = matcher.transition(labs[j].first, lb);
                            if (nextstate != -1){
                                string newlabel = labs[j].second + lb;
                                label_new[u].push_back(make_pair(nextstate, newlabel));
                            }                            
                        }
                    }
                    
                    if (vid != src){
                        vector<pair<int, string> >& rlabs = rlabel[vid];
                        int start = dis==1? 0:rpos[vid][dis-2], 
                            end = rpos[vid][dis-1];

                        for (int j=start; j<end; ++j){
                            int nextstate = matcher_r.transition(rlabs[j].first, lb);
                            if (nextstate != -1){
                                string newlabel = rlabs[j].second + lb;
                                rlabel_new[u].push_back(make_pair(nextstate, newlabel));
                            }
                        }
                    }
                }

                if (label_new[u].size() > 0 and u!=dst){
                    sort(label_new[u].begin(), label_new[u].end());
                    
                    if (s_final == 0) ResetLabel(label[u], label_new[u]); // 去重复
                    else              ResetLabelhop(label_new[u]);
                }

                if (rlabel_new[u].size() > 0 and u!=src){
                    sort(rlabel_new[u].begin(), rlabel_new[u].end());
                    
                    if (s_final == 0) ResetLabel(rlabel[u], rlabel_new[u]); 
                    else              ResetLabelhop(rlabel_new[u]); 
                }

                Cnt1[u] +=  label_new[u].size();
                Cnt2[u] += rlabel_new[u].size();
            }
        }

        omp_set_num_threads(threads);
        #	pragma omp parallel
        {
            int pid = omp_get_thread_num(), np = omp_get_num_threads();
    
            for ( int u = pid; u < totalV; u += np ){
                
                rlabel[u].insert(rlabel[u].end(), rlabel_new[u].begin(), rlabel_new[u].end());
                label[u].insert(label[u].end(), label_new[u].begin(), label_new[u].end());
                rpos[u].push_back(rlabel[u].size()), pos[u].push_back(label[u].size());

                label_new[u].clear(), rlabel_new[u].clear();
                vector<pair<int, string> >().swap(label_new[u]);
                vector<pair<int, string> >().swap(rlabel_new[u]);
            }
        }

        #pragma omp barrier
        for (int i=0; i<totalV; ++i){
            cnt1 += Cnt1[i];
            cnt2 += Cnt2[i];
        }

        // === 利用dst进行shortest distance的计算 ===
        if (mindis == 99){
            for (auto& elem: label[dst]){
                auto [f1, f2] = matcher.match(elem.second);
                if (f1){
                    mindis = dis;
                    break;
                }
            }
        }

        // cout<<"dis: "<<dis<<"  **  "<<cnt1<<"  "<<cnt2<<"  "<<mindis<<endl;
        
        Cnt1.clear(), Cnt1.resize(totalV);
        Cnt2.clear(), Cnt2.resize(totalV);

        if (cnt1 == 0 or cnt2 == 0 or dis == mindis) break;
    }
}

int hasDuplicate(vector<pair<int, char>>& vec) {
    if (vec.size() < 2) return 0;
    sort(vec.begin(), vec.end());
    for (size_t i = 1; i < vec.size(); ++i) {
        if (vec[i] == vec[i-1])
            return 1;
    }
    return 0;
}

void LabelCombine(RegexMatcher& matcher){
    
    // Nlabel[src][0] = 1;
    int actual_dis = 0;
    for (auto& elem: label[dst]){
        auto [f1, f2] = matcher.match(elem.second);
        if (f1 and actual_dis < elem.second.size())
            actual_dis = elem.second.size();
    }
    mindis = actual_dis;

    omp_set_num_threads(threads);

    #	pragma omp parallel
    {
        int pid = omp_get_thread_num(), np = omp_get_num_threads();

        for ( int u = pid; u < totalV; u += np ){

            // if (u == src or u == dst) continue;

            vector<pair<int, string> >& sLab = label[u];
            vector<pair<int, string> >& dLab = rlabel[u];

            if (sLab.size() == 0 or dLab.size() == 0) continue;
            
            for (int ii=0; ii<sLab.size(); ++ii){
                pair<int, string>& s1 = sLab[ii];

                for (int jj=0; jj<dLab.size(); ++jj){
                    pair<int, string>& d1 = dLab[jj];
                    string combined = s1.second + string(d1.second.rbegin(), d1.second.rend());
                    auto [f1, f2] = matcher.match(combined);

                    if (f1 and combined.size() <= mindis){
                        int len = s1.second.size();
                        int val = (len<<16)|s1.first;
                        Nlabel[u][val] = combined.size();
                        break;
                    }  
                }
            }
        }
    }

    omp_set_num_threads(threads);
    long long activedges = 0;
    #	pragma omp parallel
    {
        int pid = omp_get_thread_num(), np = omp_get_num_threads();

        for ( int u = pid; u < totalV; u += np ){

            if (Nlabel[u].size() == 0 or u == dst) continue;

            for (pair<int,char>& elem: con[u]){
                
                int v = elem.first;
                char lab = elem.second;

                if (!matcher.isCharPossiblyInRegex(lab)) continue;

                if ( Nlabel[v].size() == 0 ) continue;

                // activedges += 1;

                for (auto& state:Nlabel[u]){
                    int aa = state.first >> 16,
                        bb = state.first & 0xFFFF;

                    int next = matcher.transition(bb, lab),
                        len = aa + 1,
                        val = (len<<16) | next;

                    if ( Nlabel[v].find(val) != Nlabel[v].end()){
                        // 当子路径到达u且状态为state.first时，其邻居都可以访问
                        consketch[u][state.first].push_back(elem);

                    }
                }
            }
        }
    }

    active_num = 0;
    
    for (int i=0; i<totalV; ++i){
        
        if (consketch[i].size() > 0){
            old2new[i] = active_num;
            new2old[active_num] = i;
            active_num += 1;
        }
    }
    
    old2new[dst] = active_num;
    new2old[active_num] = dst;
    active_num += 1;
    cout<<"active_num: "<<active_num<<endl;
}


void LoadPredict(RegexMatcher& matcher){

    WL.resize(active_num);

    int dst_new = old2new[dst], src_new = old2new[src], cnt = 0;

    for (auto& elem: Nlabel[dst]) WL[dst_new][elem.first][cnt] = 1;

    while (cnt < mindis){

        for (int i=0; i<active_num; ++i){
            
            int u = new2old[i];
            
            for (auto& elem: consketch[u]){
                
                long long path_cnt = 0;
                
                int len_sub_u = elem.first >> 16, state_sub_u = elem.first & 0xFFFF;

                vector<pair<int, char> >& edges = elem.second;  

                for (auto& adj: edges){
                    int v = adj.first, nextState = matcher.transition(state_sub_u, adj.second);
                    int key = (len_sub_u+1)<<16 | nextState;
                    
                    if (WL[old2new[v]][key].find(cnt) == WL[old2new[v]][key].end()) 
                        continue;

                    path_cnt += WL[old2new[v]][key][cnt];
                    // cout<<old2new[v]<<" "<<active_num<<" "<<WL[old2new[v]][key][cnt]<<endl;
                }

                WL[i][elem.first][cnt+1] = path_cnt;
            }   
            
        }
        cnt += 1;
    }

    WLTotal = 0;
    for (auto& elem: WL[src_new]){
        for (auto &ac: elem.second){
            WLTotal += ac.second;
        }
    }
            
    cout<<"Predicted paths: "<<WLTotal<<"  "<<WLavg<<endl;  

    ParaDeletion();
}


void BranchHash(int u, vector<int>& Path, vector<int>& dfaStates, 
                vector<int>& visited, RegexMatcher& matcher, 
               vector<unordered_map<int, vector<pair<int, char> > > >& conR){
    Path.push_back(u);
    visited[u] = 1;

    // 计算当前负载数量

    if (Path.size() == 4){
        PathSet.push_back(Path);
        StateSet.push_back(dfaStates);
    }else{
        int curDfaState = dfaStates.back(), curdis = Path.size() - 1,
        curval = (curdis<<16)|curDfaState;

        if (conR[u].find(curval) != conR[u].end()){
            vector<pair<int, char> >& edges = conR[u][curval];

            for (auto& elem : edges) {
                int v = elem.first, 
                    nextState = matcher.transition(curDfaState, elem.second),
                    val = (Path.size() << 16) | nextState;  

                if (v == dst){
                    paths += 1;
                }else if (visited[v] == 0){
                    dfaStates.push_back(nextState);
                    BranchHash(v, Path, dfaStates, visited, matcher, conR);
                    dfaStates.pop_back();
                }
            }
        }
    }
    
    // 离开节点
    Path.pop_back();
    visited[u] = 0;
}

void BranchGenerate(int u, vector<int>& Path, vector<int>& dfaStates, 
                vector<int>& visited, RegexMatcher& matcher, 
               vector<unordered_map<int, vector<pair<int, char> > > >& conR){
    Path.push_back(u);
    visited[u] = 1;

    // 计算当前负载数量
    long long load = 0;
    for (auto& elem: WL[old2new[u]]){
        for (auto &ac: elem.second){
            if ( ac.first <= mindis+1-Path.size() )
                load += ac.second;
        }
    }

    int val = (int) load / (1000);
    if (WLavg < val) WLavg = val;

    if (load <= WLavg){
        PathSet.push_back(Path);
        StateSet.push_back(dfaStates);
    }else{
        int curDfaState = dfaStates.back(), curdis = Path.size() - 1,
        curval = (curdis<<16)|curDfaState;

        if (conR[u].find(curval) != conR[u].end()){
            vector<pair<int, char> >& edges = conR[u][curval];

            for (auto& elem : edges) {
                int v = elem.first, 
                    nextState = matcher.transition(curDfaState, elem.second),
                    val = (Path.size() << 16) | nextState;  

                if (v == dst){
                    paths += 1;
                }else if (visited[v] == 0){
                    dfaStates.push_back(nextState);
                    BranchGenerate(v, Path, dfaStates, visited, matcher, conR);
                    dfaStates.pop_back();
                }
            }
        }
    }
    
    // 离开节点
    Path.pop_back();
    visited[u] = 0;
}


void DFSearch(int u, int tgt, vector<int>& Path, 
              vector<int>& dfaStates, vector<int>& visited, RegexMatcher& matcher, 
               vector<unordered_map<int, vector<pair<int, char> > > >& conR) {
    // 进入节点
    Path.push_back(u);
    visited[u] = 1;

    int curDfaState = dfaStates.back(), curdis = Path.size() - 1,
        curval = (curdis<<16)|curDfaState;

    if (conR[u].find(curval) != conR[u].end()){
        vector<pair<int, char> >& edges = conR[u][curval];

        for (auto& elem : edges) {
            int v = elem.first, 
                nextState = matcher.transition(curDfaState, elem.second),
                val = (Path.size() << 16) | nextState;  

            if (v == tgt){
                paths += 1;
            }
            else if (visited[v] == 0 and Path.size() == mindis-1){
                paths += conR[v][val].size();
                // if (paths%50000000 == 0) cout<<paths<<"  "<<redpath<<endl;
            }
            else if (visited[v] == 0){
                dfaStates.push_back(nextState);
                DFSearch(v, tgt, Path, dfaStates, visited, matcher, conR);
                dfaStates.pop_back();
            }else if (visited[v] == 1){
                redpath += 1;
            }
        }
    }

    // 离开节点
    Path.pop_back();
    visited[u] = 0;
}

void DFSearchParallel(int u, int tgt, vector<int>& Path, 
              vector<int>& dfaStates, vector<int>& visited, 
              long long& aaa, RegexMatcher& matcher, 
               vector<unordered_map<int, vector<pair<int, char> > > >& conR) {
    // 进入节点
    Path.push_back(u);
    visited[u] = 1;

    int curDfaState = dfaStates.back(), curdis = Path.size() - 1,
        curval = (curdis<<16)|curDfaState;

    if (conR[u].find(curval) != conR[u].end()){
        vector<pair<int, char> >& edges = conR[u][curval];

        for (auto& elem : edges) {
            int v = elem.first, 
                nextState = matcher.transition(curDfaState, elem.second),
                val = (Path.size() << 16) | nextState;  

            if (v == tgt){
                aaa += 1;
            } else if (visited[v] == 0 and Path.size() == mindis-1){
                aaa += conR[v][val].size();
                // if (aaa % 1000000 == 0) cout<<aaa<<endl;
            } else if (visited[v] == 0){
                dfaStates.push_back(nextState);
                DFSearchParallel(v, tgt, Path, dfaStates, visited, aaa, matcher, conR);
                dfaStates.pop_back();
            }
        }
    }

    // 离开节点
    Path.pop_back();
    visited[u] = 0;
}

int main(int argc, char* argv[]){

    if (argc > 1) na        = argv[1];   
    if (argc > 2) aplace    = stoi(argv[2]);
    if (argc > 3) bplace    = stoi(argv[3]);
    if (argc > 4) mindis    = stoi(argv[4]);
    if (argc > 5) charPool  = argv[5];
    if (argc > 6) regex     = argv[6];
    if (argc > 7) threads   = stoi(argv[7]);
    if (argc > 8) threshold = stod(argv[8]);
    if (argc > 9) WLavg     = stod(argv[9]);

    if (mindis != 99) s_final = 1;

    name = "/mnt/data/zyy/Full/"+na+".graph";

    regex_rever = reverseRegex(regex); // regex 反转

    vector<int> stk, lab; 
    lab.push_back(0);

    RegexMatcher matcher, matcher_rever;
    matcher.build(regex);
    matcher_rever.build(regex_rever);

    statenum = matcher.stateCount();
    GraphInitial(name);
    // GraphTest(name, 2);
    
    // src = stoi(argv[2]), dst = stoi(argv[3]);
    cout<<"reverse: "<<na<<"  "<<src<<"  "<<dst<<endl;
    
    double tt1 = omp_get_wtime();

    ParallelBuild(matcher, matcher_rever);
    
    LabelCombine(matcher);

    if (active_num > 1){
        
        LoadPredict(matcher);

        if (WLTotal < threshold){
            DFSearch(src, dst, stk, lab, visited, matcher, consketch);
        }else{
            BranchGenerate(src, stk, lab, visited, matcher, consketch);
            cout<<"Subtasks: "<<PathSet.size()<<endl;
            vector<vector<int> > Visited(threads, vector<int>(totalV, 0));

            omp_set_num_threads(threads);
            #	pragma omp parallel
            {
                int pid = omp_get_thread_num(), np = omp_get_num_threads();
                
                for( int u = pid; u < PathSet.size(); u += np ){
                    vector<int>& P1 = PathSet[u];
                    vector<int>& S1 = StateSet[u];
                    long long aaa = 0;

                    int active_v = P1.back();
                    P1.pop_back();

                    for (int ii=0; ii<P1.size(); ++ii)
                        Visited[pid][P1[ii]] = 1;

                    DFSearchParallel(active_v, dst, P1, S1, Visited[pid], aaa, matcher, consketch);

                    for (int ii=0; ii<P1.size(); ++ii)
                        Visited[pid][P1[ii]] = 0;

                    # pragma omp atomic
                    paths += aaa;
                }
            }
        }
    }
    

    double elapsed = omp_get_wtime() - tt1;
    cout<<"paths: "<<paths<<endl;
    cout<<"time: "<<omp_get_wtime()-tt1<<" s"<<endl;

    string resultFile = "LargeGraph/"+ na + "_" + to_string(stoi(argv[4])) + ".txt";
    ofstream fout(resultFile, ios::app);
    if (fout.is_open()) {
        fout << na << " "
            << src << " "
            << dst << " "
            << regex << " "
            << threads << " "
            << elapsed << " "
            << paths << endl;
        fout.close();
    } else {
        cerr << "Failed to open " << resultFile << " for writing." << endl;
    }

    return 0;
}
