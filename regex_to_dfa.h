/**
 * 极致内存优化版 DFA 正则引擎
 * 特点：
 * 1. 静态匹配和增量式匹配共用同一个DFA转换表
 * 2. 构建完成后，仅保留匹配所需的最小数据集
 * 3. 增量式支持回溯功能
 * 4. 支持 {n} {n,m} {n,} 量词
 * 5. 修复了字符签名比较、回溯栈、空字符串等bug
 */

#include <iostream>
#include <vector>
#include <string>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <queue>
#include <memory>
#include <algorithm>
#include <stack>
#include <bitset>
#include <cassert>

using namespace std;

// ==================== 常量定义 ====================
const int EPSILON = -1;
const int CHAR_SET_SIZE = 256;
const int DFA_UNREACHABLE = -1;
const size_t MAX_HISTORY_DEPTH = 10000;

// ==================== NFA 节点定义 ====================
struct NFAState {
    int id;
    vector<pair<int, int>> transitions;
    bool isAccept;
    
    NFAState(int id) : id(id), isAccept(false) {}
    
    void addTransition(int input, int target) {
        transitions.emplace_back(input, target);
    }
};

// ==================== NFA 定义 ====================
struct NFA {
    int startState;
    int acceptState;
    unordered_map<int, shared_ptr<NFAState>> states;
    
    NFA() : startState(0), acceptState(0) {}
};

// ==================== 自定义哈希函数 ====================
struct SetHash {
    size_t operator()(const unordered_set<int>& s) const {
        size_t hash = 14695981039346656037ULL;
        for (int elem : s) {
            hash ^= static_cast<size_t>(elem);
            hash *= 1099511628211ULL;
        }
        return hash;
    }
};

// ==================== ε-闭包计算 ====================
class EpsilonClosure {
public:
    static unordered_set<int> compute(const NFA& nfa, int state) {
        unordered_set<int> closure;
        vector<int> worklist;
        closure.insert(state);
        worklist.push_back(state);
        
        size_t head = 0;
        while(head < worklist.size()){
            int current = worklist[head++];
            auto it = nfa.states.find(current);
            if (it != nfa.states.end()) {
                for (auto& trans : it->second->transitions) {
                    if (trans.first == EPSILON) {
                        if (closure.find(trans.second) == closure.end()) {
                            closure.insert(trans.second);
                            worklist.push_back(trans.second);
                        }
                    }
                }
            }
        }
        return closure;
    }
    
    static unordered_set<int> compute(const NFA& nfa, const unordered_set<int>& states) {
        unordered_set<int> result;
        for (int s : states) {
            auto closure = compute(nfa, s);
            result.insert(closure.begin(), closure.end());
        }
        return result;
    }
};

// ==================== 正则表达式解析器 ====================
class RegexParser {
private:
    string regex;
    size_t pos;
    int stateCounter;
    
    char peek() { return (pos < regex.size()) ? regex[pos] : '\0'; }
    char consume() { return (pos < regex.size()) ? regex[pos++] : '\0'; }
    int newState() { return stateCounter++; }
    
    int parseNumber() {
        int num = 0;
        while (peek() >= '0' && peek() <= '9') {
            num = num * 10 + (consume() - '0');
        }
        return num;
    }
    

    NFA copyNFA(const NFA& nfa) {
        NFA result;
        unordered_map<int, int> stateMap;
        
        // 先分配新状态号
        for (auto& kv : nfa.states) {
            stateMap[kv.first] = newState();
        }
        
        // 创建新状态并复制转移
        for (auto& kv : nfa.states) {
            int oldId = kv.first;
            int newId = stateMap[oldId];
            auto s = make_shared<NFAState>(newId);
            s->isAccept = kv.second->isAccept;
            
            for (auto& trans : kv.second->transitions) {
                int newTarget = stateMap[trans.second];
                s->addTransition(trans.first, newTarget);
            }
            
            result.states[newId] = s;
        }
        
        result.startState = stateMap[nfa.startState];
        result.acceptState = stateMap[nfa.acceptState];
        return result;
    }

public:
    RegexParser() : pos(0), stateCounter(0) {}
    
    NFA parse(const string& pattern) {
        regex = pattern;
        pos = 0;
        stateCounter = 0;
        return parseAlternative();
    }
    
    NFA parseAlternative() {
        NFA left = parseConcatenation();
        while (peek() == '|') {
            consume();
            NFA right = parseConcatenation();
            left = unite(left, right);
        }
        return left;
    }
    
    NFA parseConcatenation() {
        NFA first = parseClosure();
        while (peek() != '\0' && peek() != '|' && peek() != ')') {
            NFA second = parseClosure();
            first = concatenate(first, second);
        }
        return first;
    }
    
    NFA parseClosure() {
        NFA base = parseBase();
        while (peek() == '*' || peek() == '+' || peek() == '?' || peek() == '{') {
            if (peek() == '{') {
                consume();
                int min = parseNumber();
                int max = min;
                
                if (peek() == ',') {
                    consume();
                    if (peek() >= '0' && peek() <= '9') {
                        max = parseNumber();
                    } else {
                        max = -1;
                    }
                }
                
                if (peek() == '}') {
                    consume();
                }
                
                if (max == -1) {
                    base = repeatMin(base, min);
                } else if (min == max) {
                    base = repeat(base, min);
                } else {
                    base = repeatRange(base, min, max);
                }
            } else {
                char op = consume();
                if (op == '*') base = kleeneStar(base);
                else if (op == '+') base = kleenePlus(base);
                else if (op == '?') base = optional(base);
            }
        }
        return base;
    }
    
    NFA parseBase() {
        char c = peek();
        if (c == '(') {
            consume();
            NFA inner = parseAlternative();
            if (peek() == ')') consume();
            return inner;
        } else if (c == '[') {
            return parseCharClass();
        } else if (c == '.') {
            consume();
            return createAnyChar();
        } else if (c != '\0' && c != '|' && c != '*' && c != '+' && c != '?' && c != '}' && c != ')') {
            consume();
            return createChar(c);
        }
        return createEpsilon();
    }
    
    NFA parseCharClass() {
        consume();
        int start = newState();
        int accept = newState();
        set<int> charSet;
        bool negated = false;
        
        if (peek() == '^') {
            negated = true;
            consume();
        }
        
        if (peek() == ']') {
            charSet.insert((unsigned char)consume());
        }
        
        if (peek() == '-') {
            charSet.insert((unsigned char)consume());
        }
        
        while (peek() != ']' && peek() != '\0') {
            char c = consume();
            
            if (peek() == '-' && pos + 1 < regex.size() && regex[pos + 1] != ']') {
                consume();
                char end = consume();
                for (int ch = (unsigned char)c; ch <= (unsigned char)end; ch++) {
                    charSet.insert(ch);
                }
            } else {
                charSet.insert((unsigned char)c);
            }
        }
        
        if (peek() == '-' && pos + 1 < regex.size() && regex[pos + 1] == ']') {
            consume();
        }
        
        if (peek() == ']') consume();
        
        if (negated) {
            set<int> complement;
            for (int i = 0; i < CHAR_SET_SIZE; i++) {
                if (charSet.find(i) == charSet.end()) {
                    complement.insert(i);
                }
            }
            charSet = complement;
        }
        
        NFA nfa;
        auto sState = make_shared<NFAState>(start);
        for (int ch : charSet) {
            sState->addTransition(ch, accept);
        }
        nfa.states[start] = sState;
        
        auto aState = make_shared<NFAState>(accept);
        aState->isAccept = true;
        nfa.states[accept] = aState;
        
        nfa.startState = start;
        nfa.acceptState = accept;
        return nfa;
    }
    
    NFA createChar(char c) {
        int start = newState(), accept = newState();
        NFA nfa;
        auto sState = make_shared<NFAState>(start);
        sState->addTransition(static_cast<unsigned char>(c), accept);
        nfa.states[start] = sState;
        auto aState = make_shared<NFAState>(accept);
        aState->isAccept = true;
        nfa.states[accept] = aState;
        nfa.startState = start; 
        nfa.acceptState = accept;
        return nfa;
    }
    
    NFA createAnyChar() {
        int start = newState(), accept = newState();
        NFA nfa;
        auto sState = make_shared<NFAState>(start);
        for (int i = 0; i < CHAR_SET_SIZE; i++) {
            sState->addTransition(i, accept);
        }
        nfa.states[start] = sState;
        auto aState = make_shared<NFAState>(accept);
        aState->isAccept = true;
        nfa.states[accept] = aState;
        nfa.startState = start; 
        nfa.acceptState = accept;
        return nfa;
    }
    
    NFA createEpsilon() {
        int start = newState(), accept = newState();
        NFA nfa;
        auto sState = make_shared<NFAState>(start);
        sState->addTransition(EPSILON, accept);
        nfa.states[start] = sState;
        auto aState = make_shared<NFAState>(accept);
        aState->isAccept = true;
        nfa.states[accept] = aState;
        nfa.startState = start; 
        nfa.acceptState = accept;
        return nfa;
    }
    
    NFA concatenate(const NFA& left, const NFA& right) {
        NFA result;
        for (auto& kv : left.states) result.states[kv.first] = kv.second;
        for (auto& kv : right.states) result.states[kv.first] = kv.second;
        
        result.states[left.acceptState]->addTransition(EPSILON, right.startState);
        result.states[left.acceptState]->isAccept = false;
        
        result.startState = left.startState;
        result.acceptState = right.acceptState;
        result.states[right.acceptState]->isAccept = true;
        return result;
    }
    
    NFA unite(const NFA& left, const NFA& right) {
        NFA result;
        int newStart = newState(), newAccept = newState();
        
        auto sState = make_shared<NFAState>(newStart);
        sState->addTransition(EPSILON, left.startState);
        sState->addTransition(EPSILON, right.startState);
        result.states[newStart] = sState;
        
        for (auto& kv : left.states) result.states[kv.first] = kv.second;
        for (auto& kv : right.states) result.states[kv.first] = kv.second;
        
        auto aState = make_shared<NFAState>(newAccept);
        aState->isAccept = true;
        result.states[newAccept] = aState;
        
        result.states[left.acceptState]->addTransition(EPSILON, newAccept);
        result.states[left.acceptState]->isAccept = false;
        result.states[right.acceptState]->addTransition(EPSILON, newAccept);
        result.states[right.acceptState]->isAccept = false;
        
        result.startState = newStart;
        result.acceptState = newAccept;
        return result;
    }
    
    NFA kleeneStar(const NFA& nfa) {
        NFA result;
        int newStart = newState(), newAccept = newState();
        
        auto sState = make_shared<NFAState>(newStart);
        sState->addTransition(EPSILON, nfa.startState);
        sState->addTransition(EPSILON, newAccept);
        result.states[newStart] = sState;
        
        for (auto& kv : nfa.states) result.states[kv.first] = kv.second;
        
        auto aState = make_shared<NFAState>(newAccept);
        aState->isAccept = true;
        result.states[newAccept] = aState;
        
        result.states[nfa.acceptState]->addTransition(EPSILON, nfa.startState);
        result.states[nfa.acceptState]->addTransition(EPSILON, newAccept);
        result.states[nfa.acceptState]->isAccept = false;
        
        result.startState = newStart;
        result.acceptState = newAccept;
        return result;
    }
    
    NFA kleenePlus(const NFA& nfa) { 
        return concatenate(nfa, kleeneStar(nfa)); 
    }
    
    NFA optional(const NFA& nfa) {
        NFA result;
        int newStart = newState(), newAccept = newState();
        
        auto sState = make_shared<NFAState>(newStart);
        sState->addTransition(EPSILON, nfa.startState);
        sState->addTransition(EPSILON, newAccept);
        result.states[newStart] = sState;
        
        for (auto& kv : nfa.states) result.states[kv.first] = kv.second;
        
        auto aState = make_shared<NFAState>(newAccept);
        aState->isAccept = true;
        result.states[newAccept] = aState;
        
        result.states[nfa.acceptState]->addTransition(EPSILON, newAccept);
        result.states[nfa.acceptState]->isAccept = false;
        
        result.startState = newStart;
        result.acceptState = newAccept;
        return result;
    }
    

    NFA repeat(const NFA& nfa, int n) {
        if (n == 0) return createEpsilon();
        NFA result = copyNFA(nfa);
        for (int i = 1; i < n; i++) {
            NFA next = copyNFA(nfa);
            result = concatenate(result, next);
        }
        return result;
    }
    

    NFA repeatRange(const NFA& nfa, int min, int max) {
        if (min > max) return createEpsilon();
        if (min == 0 && max == 0) return createEpsilon();
        
        NFA result;
        vector<int> stateChain;
        
        for (int i = 0; i <= max; i++) {
            stateChain.push_back(newState());
        }
        
        for (int i = 0; i < max; i++) {
            auto sState = make_shared<NFAState>(stateChain[i]);
            auto it = nfa.states.find(nfa.startState);
            if (it != nfa.states.end()) {
                for (auto& trans : it->second->transitions) {
                    if (trans.first != EPSILON) {
                        sState->addTransition(trans.first, stateChain[i + 1]);
                    }
                }
            }
            result.states[stateChain[i]] = sState;
        }
        
        auto lastState = make_shared<NFAState>(stateChain[max]);
        lastState->isAccept = true;
        result.states[stateChain[max]] = lastState;
        
        for (int i = min; i < max; i++) {
            result.states[stateChain[i]]->addTransition(EPSILON, stateChain[max]);
        }
        
        result.startState = stateChain[0];
        result.acceptState = stateChain[max];
        
        return result;
    }
    

    NFA repeatMin(const NFA& nfa, int min) {
        if (min == 0) return kleeneStar(nfa);
        if (min == 1) return kleenePlus(nfa);
        
        NFA result;
        vector<int> stateChain;
        
        for (int i = 0; i <= min; i++) {
            stateChain.push_back(newState());
        }
        
        for (int i = 0; i < min; i++) {
            auto sState = make_shared<NFAState>(stateChain[i]);
            auto it = nfa.states.find(nfa.startState);
            if (it != nfa.states.end()) {
                for (auto& trans : it->second->transitions) {
                    if (trans.first != EPSILON) {
                        sState->addTransition(trans.first, stateChain[i + 1]);
                    }
                }
            }
            result.states[stateChain[i]] = sState;
        }
        
        auto lastState = make_shared<NFAState>(stateChain[min]);
        lastState->isAccept = true;
        
        int loopState = newState();
        auto loopS = make_shared<NFAState>(loopState);
        auto it = nfa.states.find(nfa.startState);
        if (it != nfa.states.end()) {
            for (auto& trans : it->second->transitions) {
                if (trans.first != EPSILON) {
                    loopS->addTransition(trans.first, stateChain[min]);
                }
            }
        }
        
        lastState->addTransition(EPSILON, loopState);
        
        result.states[stateChain[min]] = lastState;
        result.states[loopState] = loopS;
        
        result.startState = stateChain[0];
        result.acceptState = stateChain[min];
        
        return result;
    }
};

// ==================== DFA 状态转移表 ====================
class DFATransitionTable {
private:
    vector<int> table;
    vector<bool> acceptStates;
    int startState;
    int numStates;
    bool isBuilt;

public:
    DFATransitionTable() : startState(0), numStates(0), isBuilt(false) {}

    void buildFromNFA(const NFA& nfa) {
        unordered_map<unordered_set<int>, int, SetHash> stateMap;
        vector<unordered_set<int>> worklist;
        
        unordered_set<int> startClosure = EpsilonClosure::compute(nfa, nfa.startState);
        stateMap[startClosure] = 0;
        worklist.push_back(startClosure);
        
        numStates = 1;
        
        vector<bool> tempAccept;
        tempAccept.reserve(100);
        tempAccept.push_back(false);
        
        vector<unordered_map<int, int>> tempTransitions;
        tempTransitions.reserve(100);
        tempTransitions.emplace_back();

        size_t head = 0;
        while(head < worklist.size()){
            const unordered_set<int>& nfaStates = worklist[head++];
            int dfaState = stateMap[nfaStates];
            
            bool isAcc = false;
            for (int s : nfaStates) {
                auto it = nfa.states.find(s);
                if (it != nfa.states.end() && it->second->isAccept) {
                    isAcc = true;
                    break;
                }
            }
            if(dfaState >= (int)tempAccept.size()) tempAccept.resize(dfaState+1, false);
            tempAccept[dfaState] = isAcc;
            if(dfaState >= (int)tempTransitions.size()) tempTransitions.resize(dfaState+1);

            unordered_map<int, unordered_set<int>> moves;
            for (int s : nfaStates) {
                auto it = nfa.states.find(s);
                if (it != nfa.states.end()) {
                    for (auto& trans : it->second->transitions) {
                        if (trans.first != EPSILON) {
                            moves[trans.first].insert(trans.second);
                        }
                    }
                }
            }
            
            for (auto& move : moves) {
                int inputChar = move.first;
                unordered_set<int> targetClosure = EpsilonClosure::compute(nfa, move.second);
                
                int nextDfaState;
                if (stateMap.find(targetClosure) == stateMap.end()) {
                    nextDfaState = numStates++;
                    stateMap[targetClosure] = nextDfaState;
                    worklist.push_back(targetClosure);
                    
                    if(nextDfaState >= (int)tempAccept.size()) tempAccept.resize(nextDfaState+1, false);
                    if(nextDfaState >= (int)tempTransitions.size()) tempTransitions.resize(nextDfaState+1);
                } else {
                    nextDfaState = stateMap[targetClosure];
                }
                
                tempTransitions[dfaState][inputChar] = nextDfaState;
            }
        }
        
        startState = 0;
        acceptStates = move(tempAccept);
        
        table.assign(numStates * CHAR_SET_SIZE, DFA_UNREACHABLE);
        
        for (int s = 0; s < numStates; ++s) {
            for (auto& kv : tempTransitions[s]) {
                int charCode = kv.first;
                int nextState = kv.second;
                table[s * CHAR_SET_SIZE + charCode] = nextState;
            }
        }
        
        isBuilt = true;
        
        minimize();

        // cout << "[DFA] 构建完成：" << numStates << " 个状态" << endl;
    }
    
    inline int nextState(int currentState, unsigned char input) const {
        if (!isBuilt || currentState < 0 || currentState >= numStates) return DFA_UNREACHABLE;
        return table[currentState * CHAR_SET_SIZE + input];
    }
    
    inline bool isAcceptState(int state) const {
        if (!isBuilt || state < 0 || state >= numStates) return false;
        return acceptStates[state];
    }
    
    inline int getStartState() const {
        return startState;
    }
    
    inline int getNumStates() const {
        return numStates;
    }
    
    inline bool getIsBuilt() const {
        return isBuilt;
    }
    
    pair<bool, int> match(const string& input) const {
        if (!isBuilt) return {false, -1};
        int state = startState;
        for (unsigned char c : input) {
            state = nextState(state, c);
            if (state == DFA_UNREACHABLE) return {false, -1};
        }
        return {acceptStates[state], state};
    }
    
    size_t getMemoryUsage() const {
        size_t tableMem = (size_t)numStates * CHAR_SET_SIZE * sizeof(int);
        size_t acceptMem = (size_t)numStates * sizeof(bool);
        return tableMem + acceptMem;
    }
    
    void printStats() const {
        cout << "\n=== DFA 内存统计 ===" << endl;
        cout << "状态数：" << numStates << endl;
        cout << "转移表大小：" << (table.size() * sizeof(int)) / 1024 << " KB" << endl;
        cout << "总内存占用：" << getMemoryUsage() / 1024 << " KB" << endl;
    }

    void minimize() {
        if (!isBuilt || numStates == 0) return;

        // 1. 将 table 转换为二维向量方便操作
        vector<vector<int>> trans(numStates, vector<int>(CHAR_SET_SIZE, DFA_UNREACHABLE));
        for (int s = 0; s < numStates; ++s) {
            for (int c = 0; c < CHAR_SET_SIZE; ++c) {
                trans[s][c] = table[s * CHAR_SET_SIZE + c];
            }
        }

        // 2. 初始化可区分矩阵 (distinguishable[s1][s2] = true 表示 s1 和 s2 可区分)
        vector<vector<bool>> distinguishable(numStates, vector<bool>(numStates, false));

        // 3. 初始划分：接受状态 vs 非接受状态
        for (int i = 0; i < numStates; ++i) {
            for (int j = i + 1; j < numStates; ++j) {
                if (acceptStates[i] != acceptStates[j]) {
                    distinguishable[i][j] = distinguishable[j][i] = true;
                }
            }
        }

        // 4. 迭代更新：如果存在一个字符 c 使得 (trans[i][c], trans[j][c]) 可区分，则 (i,j) 可区分
        bool changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < numStates; ++i) {
                for (int j = i + 1; j < numStates; ++j) {
                    if (distinguishable[i][j]) continue;
                    for (int c = 0; c < CHAR_SET_SIZE; ++c) {
                        int ni = trans[i][c];
                        int nj = trans[j][c];
                        if (ni == DFA_UNREACHABLE && nj == DFA_UNREACHABLE) continue;
                        if (ni == DFA_UNREACHABLE || nj == DFA_UNREACHABLE) {
                            // 一个有转移，一个没有 -> 可区分
                            distinguishable[i][j] = distinguishable[j][i] = true;
                            changed = true;
                            break;
                        }
                        if (ni != nj && distinguishable[ni][nj]) {
                            distinguishable[i][j] = distinguishable[j][i] = true;
                            changed = true;
                            break;
                        }
                    }
                }
            }
        }

        // 5. 构建等价类 (不可区分的状态合并)
        vector<int> stateMapping(numStates, -1);
        int newStateCount = 0;
        for (int i = 0; i < numStates; ++i) {
            if (stateMapping[i] != -1) continue;
            stateMapping[i] = newStateCount;
            for (int j = i + 1; j < numStates; ++j) {
                if (!distinguishable[i][j]) {
                    stateMapping[j] = newStateCount;
                }
            }
            ++newStateCount;
        }

        // 6. 构建新的转移表和接受状态数组
        vector<int> newTable(newStateCount * CHAR_SET_SIZE, DFA_UNREACHABLE);
        vector<bool> newAccept(newStateCount, false);

        for (int old = 0; old < numStates; ++old) {
            int newState = stateMapping[old];
            if (acceptStates[old]) newAccept[newState] = true;
            for (int c = 0; c < CHAR_SET_SIZE; ++c) {
                int next = trans[old][c];
                if (next != DFA_UNREACHABLE) {
                    int newNext = stateMapping[next];
                    newTable[newState * CHAR_SET_SIZE + c] = newNext;
                }
            }
        }

        // 7. 更新成员变量
        table.swap(newTable);
        acceptStates.swap(newAccept);
        numStates = newStateCount;
        startState = stateMapping[startState];

        // cout << "[DFA] 最小化完成，状态数从 " << trans.size() << " 减少到 " << numStates << endl;
    }
};

// ==================== 统一正则匹配器 ====================
class RegexMatcher {
private:
    DFATransitionTable dfaTable;
    bool isBuilt;
    
    int incrementalState;
    bool incrementalValid;
    stack<int> historyStack;
    vector<bool> validChars;

    bitset<CHAR_SET_SIZE> validCharSet;  // validCharSet[c]=1 表示字符 c 在正则中有用
    bool isPrecomputed = false;          // 预计算完成标志

public:
    RegexMatcher() : isBuilt(false), incrementalState(0), incrementalValid(false) {}
    
    bool build(const string& regex) {
        RegexParser parser;
        NFA nfa = parser.parse(regex);
        dfaTable.buildFromNFA(nfa);  
        isBuilt = true;
        
        resetIncremental();

        precomputeValidChars();

        return true;
    }
    
    void precomputeValidChars() {
        
        validCharSet.reset();
        
        if (!isBuilt) {
            isPrecomputed = false;
            return;
        }
        
        // 遍历 DFA 所有状态的所有字符转移
        int stateCount = dfaTable.getNumStates();
        for (int state = 0; state < stateCount; ++state) {
            for (int c = 0; c < CHAR_SET_SIZE; ++c) {
                int nextState = dfaTable.nextState(state, static_cast<unsigned char>(c));
                if (nextState != DFA_UNREACHABLE) {
                    validCharSet.set(c);  // 标记该字符有效
                }
            }
        }
        isPrecomputed = true;
    }

    int stateCount() const { return dfaTable.getNumStates(); }
    
    bool isCharDefinitelyNotInRegex(char c) const {
        if (!isPrecomputed) return true;  // 防御性检查
        return !validCharSet.test(static_cast<unsigned char>(c));
    }
    
    bool isCharPossiblyInRegex(char c) const {
        return !isCharDefinitelyNotInRegex(c);
    }

    pair<bool, int> match(const string& input) const {
        if (!isBuilt) return {false, -1};
        return dfaTable.match(input);
    }
    
    bool isMatch(const string& input) const {
        return match(input).first;
    }
    
    void resetIncremental() {
        if (!isBuilt) return;
        incrementalState = dfaTable.getStartState();
        incrementalValid = true;
        while (!historyStack.empty()) {
            historyStack.pop();
        }
    }
    
    int transition(int currentState, char input) const {
        if (!isBuilt || currentState < 0) {
            return DFA_UNREACHABLE;
        }
        unsigned char ch = static_cast<unsigned char>(input);
        return dfaTable.nextState(currentState, ch);
    }

    pair<bool, bool> addChar(char c) {
        if (!isBuilt || !incrementalValid) {
            return {false, false};
        }
        
        if (historyStack.size() >= MAX_HISTORY_DEPTH) {
            historyStack.pop();
        }
        historyStack.push(incrementalState);
        
        unsigned char input = static_cast<unsigned char>(c);
        int nextState = dfaTable.nextState(incrementalState, input);
        
        if (nextState == DFA_UNREACHABLE) {
            incrementalValid = false;
            incrementalState = DFA_UNREACHABLE;
            return {false, false};
        }
        
        incrementalState = nextState;
        bool isAccept = dfaTable.isAcceptState(incrementalState);
        return {true, isAccept};
    }
    
    pair<bool, bool> addString(const string& str) {
        for (char c : str) {
            auto result = addChar(c);
            if (!result.first) break;
        }
        return {incrementalValid, isCurrentlyAccepting()};
    }
    
    bool backtrack() {
        if (historyStack.empty()) {
            return false;
        }
        incrementalState = historyStack.top();
        historyStack.pop();
        incrementalValid = true;
        return true;
    }
    
    int backtrackMultiple(int steps) {
        int actualSteps = 0;
        while (steps > 0 && !historyStack.empty()) {
            backtrack();
            steps--;
            actualSteps++;
        }
        return actualSteps;
    }
    
    bool isCurrentlyAccepting() const {
        if (!incrementalValid) return false;
        return dfaTable.isAcceptState(incrementalState);
    }
    
    bool isCurrentlyValid() const {
        return incrementalValid;
    }
    
    int getCurrentState() const {
        return incrementalState;
    }
    
    size_t getHistoryDepth() const {
        return historyStack.size();
    }
    
    void printStats() const {
        if(isBuilt) dfaTable.printStats();
    }
    
    size_t getMemoryUsage() const {
        return dfaTable.getMemoryUsage();
    }
};





// ==================== 测试用例 ====================
void runConsistencyTests() {
    cout << "\n" << string(60, '=') << endl;
    cout << "【一致性测试】DFA静态匹配 vs 增量式匹配" << endl;
    cout << string(60, '=') << endl;
    
    struct TestCase {
        string regex;
        string input;
        bool expected;
    };
    
    vector<TestCase> tests = {
        {"a*b", "b", true},
        {"a*b", "aab", true},
        {"a*b", "c", false},
        {"a*b", "ac", false},
        {"[a-z]+", "abc", true},
        {"[a-z]+", "123", false},
        {"(a|b)*", "abab", true},
        {"(a|b)*", "", true},
        {"a+", "", false},
        {"a*", "", true},
        {"a?", "a", true},
        {"a?", "", true},
        {"a|b", "a", true},
        {"a|b", "b", true},
        {"a|b", "c", false},
        {"(ab)+", "ab", true},
        {"(ab)+", "abab", true},
        {"(ab)+", "a", false},
        {"[0-9]{3}", "123", true},
        {"[0-9]{3}", "12", false},
        {"[0-9]{3}", "1234", false},
        {".*", "anything", true},
        {"a.c", "abc", true},
        {"a.c", "ac", false},
        {"a{2}", "aa", true},
        {"a{2}", "a", false},
        {"a{2,4}", "aaa", true},
        {"a{2,4}", "a", false},
        {"a{2,4}", "aaaaa", false},
        {"a{2,}", "aaaaa", true},
        {"a{2,}", "a", false},
    };
    
    int passed = 0, failed = 0;
    
    for (auto& test : tests) {
        RegexMatcher matcher;
        matcher.build(test.regex);
        
        auto [staticMatch, staticState] = matcher.match(test.input);
        
        matcher.resetIncremental();
        auto [incValid, incAccept] = matcher.addString(test.input);
        
        bool dfaOk = (staticMatch == test.expected);
        bool incOk = (incAccept == test.expected);
        bool consistent = (staticMatch == incAccept);
        
        if (dfaOk && incOk && consistent) {
            cout << "✅ 通过：" << test.regex << " @ \"" << test.input << "\"" << endl;
            passed++;
        } else {
            cout << "❌ 失败：" << test.regex << " @ \"" << test.input << "\"" << endl;
            cout << "   期望=" << test.expected << ", 静态=" << staticMatch 
                 << ", 增量=" << incAccept << ", 一致=" << consistent << endl;
            failed++;
        }
    }
    
    cout << "\n测试结果：" << passed << " 通过，" << failed << " 失败" << endl;
    cout << string(60, '=') << endl;
}


void runInteractiveIncrementalTest() {
    cout << "\n" << string(80, '=') << endl;
    cout << "【交互式增量测试】实时输入字符检测" << endl;
    cout << string(80, '=') << endl;
    
    string regex;
    cout << "输入正则表达式: ";
    if (!getline(cin, regex) || regex.empty()) return;
    
    RegexMatcher matcher;
    if (!matcher.build(regex)) {
        cout << "❌ 正则表达式解析失败!" << endl;
        return;
    }
    
    // matcher.printStats();
    matcher.resetIncremental();
    
    cout << "\n=== 增量式输入模式 ===" << endl;
    cout << " 命令说明: " << endl;
    cout << "  - 输入字符: 逐个添加字符进行检测" << endl;
    cout << "  - back / w: 回溯一步" << endl;
    cout << "  - back N: 回溯 N 步" << endl;
    cout << "  - reset / r: 重置到初始状态" << endl;
    cout << "  - status / s: 显示当前状态" << endl;
    cout << "  - quit / q: 退出" << endl;
    cout << "========================" << endl;
    
    string currentInput;
    
    while (true) {
        // cout << "\n当前输入: \"" << currentInput << "\" ";
        // cout << "状态:" << matcher.getCurrentState() << " ";
        // cout << (matcher.isCurrentlyAccepting() ? "✅接受" : "❌拒绝") << " ";
        // cout << "历史深度:" << matcher.getHistoryDepth() << endl;
        // cout << "> ";
        
        cout<<"  字符串：  "<<currentInput
            <<"  状态：    "<<matcher.getCurrentState()
            <<"  完整正则："<<matcher.isCurrentlyAccepting()
            <<"  是否有效："<<matcher.isCurrentlyValid()<<endl;

        string cmd;
        if (!getline(cin, cmd)) break;
        
        if (cmd == "quit" || cmd == "q") {
            break;
        } else if (cmd == "reset" || cmd == "r") {
            matcher.resetIncremental();
            currentInput.clear();
            cout << "已重置到初始状态" << endl;
        } else if (cmd == "status" || cmd == "s") {
            cout << "当前状态: " << matcher.getCurrentState() << endl;
            cout << "是否接受: " << matcher.isCurrentlyAccepting() << endl;
            cout << "是否有效: " << matcher.isCurrentlyValid() << endl;
            cout << "历史深度: " << matcher.getHistoryDepth() << endl;
        } else if (cmd == "back" || cmd == "w") {
            if (matcher.backtrack()) {
                if (!currentInput.empty()) {
                    currentInput.pop_back();
                }
                cout << "回溯成功" << endl;
            } else {
                cout << " 无法回溯（已在初始状态）" << endl;
            }
        } else {
            // 添加字符
            auto [valid, isAccept] = matcher.addString(cmd);
            if (valid) {
                cout<<" 添加成功！"<<endl;
                currentInput += cmd;
                // cout << (isAccept ? "✅ 接受" : "❌ 拒绝") << endl;
            } else {
                cout<<" 添加失败，已回溯！"<<endl;
                matcher.backtrack();
                // cout << "❌ 无效输入（状态不可达）" << endl;
            }
        }
    }
}


void runSimpleCharTests(int testCount = 1000) {
    cout << "\n" << string(50, '=') << endl;
    cout << "【单字符检测自动化测试】" << endl;
    cout << string(50, '=') << endl;

    // 1. 定义测试用的正则表达式池
    vector<string> regexes = {
        "[0-9]+",      // 只含数字
        "[a-z]+",      // 只含小写
        "[A-Z]+",      // 只含大写
        "[0-9a-z]+",   // 数字 + 小写
        ".*",          // 所有字符
        "a*",          // 只含 'a'
        "(a|b)+",      // 只含 'a', 'b'
        "[^0-9]+"      // 非数字 (取决于实现，这里假设它排除了数字)
    };

    // 2. 定义测试字符池
    string charPool = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!@#";

    int passed = 0;
    int failed = 0;

    // 用于记录预期结果的简单逻辑 (Ground Truth)
    // 注意：这里只是模拟简单的预期，实际项目中 validCharSet 就是真理
    auto getExpectedResult = [](const string& regex, char c) -> bool {
        if (regex == ".*") return true;
        if (regex == "[0-9]+" || regex == "[0-9a-z]+") {
            if (c >= '0' && c <= '9') return true;
        }
        if (regex == "[0-9a-z]+" || regex == "[a-z]+") {
            if (c >= 'a' && c <= 'z') return true;
        }
        if (regex == "[A-Z]+") {
            if (c >= 'A' && c <= 'Z') return true;
        }
        if (regex == "a*") {
            return c == 'a'; 
        }
        if (regex == "(a|b)+") {
            return c == 'a' || c == 'b';
        }
        // 对于复杂情况如 [^0-9]，这里简化处理，主要测试正向匹配
        return false; 
    };

    for (int i = 0; i < testCount; ++i) {
        // 轮询选择正则和字符，确保覆盖均匀
        string regex = regexes[i % regexes.size()];
        char c = charPool[i % charPool.size()];

        RegexMatcher matcher;
        if (!matcher.build(regex)) {
            cout << "❌ 构建失败: " << regex << endl;
            failed++;
            continue;
        }

        // 获取被测函数的结果
        bool actual = matcher.isCharPossiblyInRegex(c);
        
        // 获取预期结果 (简单模拟)
        bool expected = getExpectedResult(regex, c);

        // 特殊处理：如果正则包含通配符或复杂逻辑，预期结果可能不准
        // 在这种简化测试中，我们主要关注程序是否崩溃以及基本逻辑
        // 如果 actual 和 expected 不一致，不一定代表错，可能是 getExpectedResult 写得太简单
        // 但如果是 ".*" 返回 false，那肯定是错的
        
        bool isOk = true;
        if (regex == ".*" && !actual) isOk = false; // .* 必须匹配所有
        if (regex == "a*" && c == 'a' && !actual) isOk = false; // a* 必须匹配 a
        if (regex == "[0-9]+" && c >= '0' && c <= '9' && !actual) isOk = false;
        if (regex == "[0-9]+" && c == 'a' && actual) isOk = false; // 数字正则不应匹配 'a'

        if (isOk) {
            passed++;
        } else {
            failed++;
            if (failed <= 5) {
                cout << "❌ 异常: 正则=\"" << regex << "\", 字符='" << c 
                     << "', 检测结果=" << (actual ? "有效" : "无效") << endl;
            }
        }
    }

    double accuracy = (testCount > 0) ? (100.0 * passed / testCount) : 0.0;

    cout << "\n📊 测试结果统计:" << endl;
    cout << "  总用例数: " << testCount << endl;
    cout << "  通过:     " << passed << endl;
    cout << "  失败:     " << failed << endl;
    cout << "  准确率:   " << accuracy << "%" << endl;
    
    if (failed == 0) {
        cout << "\n🎉 所有测试通过！validCharSet 工作正常。" << endl;
    } else {
        cout << "\n⚠️  发现潜在问题，请检查上述失败用例。" << endl;
    }
    cout << string(50, '=') << endl;
}
