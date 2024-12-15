/*
 */

#include <signal.h>
#include <sys/time.h>

#include <algorithm>
#include <cassert>
#include <condition_variable>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>
// #define DEBUG

// #define GoalCount
#define FF

using namespace std;

const int thread_num = 16;
const int hash_distribute_num = thread_num;

const double time_limit = 60 * 5;

const int INF = 1 << 30;

// debug methods
// usage: debug(x,y);
#define CHOOSE(a) CHOOSE2 a
#define CHOOSE2(a0, a1, a2, a3, a4, x, ...) x
#define debug_1(x1) cout << "#" << #x1 << ": " << x1 << endl
#define debug_2(x1, x2) \
    cout << "#" << #x1 << ": " << x1 << ", " #x2 << ": " << x2 << endl
#define debug_3(x1, x2, x3)                                                \
    cout << "#" << #x1 << ": " << x1 << ", " #x2 << ": " << x2 << ", " #x3 \
         << ": " << x3 << endl
#define debug_4(x1, x2, x3, x4)                                            \
    cout << "#" << #x1 << ": " << x1 << ", " #x2 << ": " << x2 << ", " #x3 \
         << ": " << x3 << ", " #x4 << ": " << x4 << endl
#define debug_5(x1, x2, x3, x4, x5)                                        \
    cout << "#" << #x1 << ": " << x1 << ", " #x2 << ": " << x2 << ", " #x3 \
         << ": " << x3 << ", " #x4 << ": " << x4 << ", " #x5 << ": " << x5 \
         << endl
#ifdef _DEBUG
#define debug(...)                                                        \
    CHOOSE((__VA_ARGS__, debug_5, debug_4, debug_3, debug_2, debug_1, ~)) \
    (__VA_ARGS__)
#else
#define debug(...)
#endif

timespec start_time;

int n;  // the number of finite-domain variables
bool metric;
int fact_num;
vector<int> fact_acc;
vector<short> variable_range;
vector<vector<pair<int, short>>> mutex_pair;
map<pair<int, short>, vector<pair<int, short>>> mutex_map;
int mutex_num;  // the number of mutex groups
vector<short> start;
int goal_number;
vector<short> goal;
vector<pair<int, short>> goal_pair;
int op;                          // the number of operators in the
vector<string> op_name;          // the name of the operaton
vector<vector<short>> pre_op_f;  // preconditions
vector<vector<pair<int, short>>> pre_op_pairs;  // pre_op_bから-1を消したもの
vector<vector<pair<int, short>>> eff_op_f;  // effect
vector<vector<pair<int, short>>> pre_op_b;  // preconditions
vector<vector<short>> eff_op_b;             // effect
vector<vector<pair<int, short>>> eff_op_b_pairs;

vector<int> action_cost;
int axiom;
bool found_solution = false;
vector<vector<int>> Hash_table;

// Relaxation_Heuristic
vector<vector<vector<int>>> g_to_a;
vector<vector<vector<int>>> dp_g;
vector<vector<vector<int>>> best_supporter_function;
vector<vector<vector<bool>>> close_ff;

double calculate_time();
void make_HashTable();
int calc_hash(const vector<short>&);
void make_Trie();
vector<pair<int, short>> check_mutex(vector<short>&);
void build_factacc();
set<pair<int, int>> operator_mutex(int&);
pair<vector<short>, int> effect_f(vector<short>,
                                  const vector<pair<int, short>>&, int);
vector<pair<int, short>> make_fact(vector<short>&);
int H_GoalCount(const vector<short>&, const vector<pair<int, short>>&);
int H_FF(const vector<short>&, const vector<pair<int, short>>&, vector<short>&,
         const int&);
int Heuristic(const vector<short>&, const vector<pair<int, short>>&,
              vector<short>& back_state = goal);
int Heuristic_r(const vector<short>&, const vector<pair<int, short>>&,
                vector<short>& back_state = goal);
bool GoalCheck(const vector<short>&,
               const vector<pair<int, short>>& back_state_pair = goal_pair);
bool operatable(const vector<short>&, const vector<pair<int, short>>);
bool ans_check(const vector<int>&);
int input();
void write_file(const string&);

// vector<short> state;
// int prev_id;
// int prev_operator;
// int id;
// int hash;
// int hash_distribution
// int par_hash_distribution
struct State {
    vector<short> state;
    int prev_id;
    int prev_operator;
    int id;
    int hash;
    int hash_distribution;
    int par_hash_distribution;
    State(const vector<short>& state, const int prev_id,
          const int prev_operator, const int id, const int hash,
          const int hash_distribution, const int par_hash_distribution)
        : state(state),
          prev_id(prev_id),
          prev_operator(prev_operator),
          id(id),
          hash(hash),
          hash_distribution(hash_distribution),
          par_hash_distribution(par_hash_distribution){};
};

struct Trie_f {
    struct Node {
        map<pair<int, short>, int> next;
        vector<int> accept;
        vector<pair<pair<int, short>, int>> next_pair;
        vector<int> next_fact;
        int node_id, start;
        bool small;
        Node(int id, int start) : node_id(id), start(start), small(false){};
        ~Node(){};
    };
    vector<Node> nodes;
    int root;
    Trie_f() : root(0) {
        nodes.push_back(Node(root, 0));
    };

    void insert(const vector<pair<int, short>>& p, const int op_id) {
        int node_id = 0;

        for (int i = 0; i < (int)p.size(); i++) {
            int next_id = nodes[node_id].next[p[i]];
            if (next_id == 0) {
                next_id = (int)nodes.size();
                Node next_node(next_id, p[i].first);
                nodes.push_back(next_node);
                nodes[node_id].next[p[i]] = next_id;
            }
            node_id = next_id;
        }
        nodes[node_id].accept.push_back(op_id);
    }

    void search(const vector<short>& state, vector<int>& operatable,
                int node_id = 0) {
        for (auto op_id : nodes[node_id].accept) {
            operatable.push_back(op_id);
        }
        if (nodes[node_id].small) {
            for (auto& [p, next_id] : nodes[node_id].next_pair) {
                if (state[p.first] == p.second)
                    search(state, operatable, next_id);
            }
        } else {
            for (int i = nodes[node_id].start; i < n; i++) {
                int next_id = nodes[node_id].next_fact[fact_acc[i] + state[i]];
                if (next_id != -1) search(state, operatable, next_id);
            }
        }
        return;
    }
    void build() {
        for (auto& node : nodes) {
            if ((int)node.next.size() <= n - node.start) {
                node.small = true;
                for (auto& [p, next_id] : node.next) {
                    node.next_pair.push_back({p, next_id});
                }
            } else {
                node.next_fact.resize(fact_num, -1);
                for (auto& [p, next_id] : node.next) {
                    node.next_fact[fact_acc[p.first] + p.second] = next_id;
                }
            }
        }
    }
};

struct OPEN {
    bool aborted;
    OPEN() : aborted(false) {
    }
    void abort() {
        aborted = true;
    }
};

template <typename T>
struct OPEN_Arrays : OPEN {
    vector<queue<T>> Heap;
    int best;
    int cnt;
    multiset<int> mn;
    OPEN_Arrays() : best(INF), cnt(0) {
        mn.insert(INF);
    }

    void _push(const pair<int, T> data, const int thread_id = -1) {
        int key = data.first;
        T value = data.second;
        ++cnt;
        if (key < best) best = key;
        if (key >= (int)Heap.size()) Heap.resize(key + 1);
        Heap[key].push(value);
    }

    void push(const pair<int, T> data, const int thread_id = -1) {
        _push(data, thread_id);
    }

    pair<int, T> _pop() {
        while (Heap[best].empty()) ++best;
        pair<int, T> data = make_pair(best, Heap[best].front());
        Heap[best].pop();
        --cnt;
        return data;
    }

    pair<int, T> pop(const int thread_id = -1) {
        if (aborted) return {-2, T()};  // no solution
        if (thread_id != -1) {
            if (cnt == 0) {
                if (mn.size() == 1) {  // no solution
                    aborted = true;
                    return {-2, T()};
                }
                return {-1, T()};
            }
            if (top() <= min()) return _pop();
            return {-1, T()};
        }
        if (cnt == 0) {
            return {-1, T()};
        }
        return _pop();
    }

    int size() {
        return cnt;
    }

    int top() {
        if (cnt == 0) return INF;
        while (Heap[best].empty()) ++best;
        return best;
    }

    int min() {
        return *mn.begin();
    }
};

template <typename T>
struct OPEN_Arrays2 : OPEN {
    vector<vector<deque<T>>> Heap;
    int best;
    int cnt;
    vector<int> bests;
    vector<int> cnts;
    multiset<int> mn;
    mutex mtx;
    OPEN_Arrays2() : best(INF), cnt(0) {
        mn.insert(INF);
    }

    void _push(const int key1, const int key2, const T data) {
        cnt++;
        if (key1 < best) best = key1;
        if (key1 >= (int)Heap.size()) {
            Heap.resize(key1 + 1);
            cnts.resize(key1 + 1);
            bests.resize(key1 + 1, INF);
        }

        cnts[key1]++;
        if (key2 < bests[key1]) bests[key1] = key2;
        if (key2 >= (int)Heap[key1].size()) {
            Heap[key1].resize(key2 + 1);
        }
        Heap[key1][key2].push_back(data);
    }

    void push(int key1, int key2, const T data, const int thread_id = -1) {
        _push(key1, key2, data);
    }

    pair<pair<int, int>, T> _pop() {
        while (cnts[best] == 0) best++;
        cnt--;
        while (Heap[best][bests[best]].empty()) bests[best]++;
        pair<pair<int, int>, T> res = {{best, bests[best]},
                                       Heap[best][bests[best]].front()};
        Heap[best][bests[best]].pop_front();
        cnts[best]--;
        return res;
    }
    pair<pair<int, int>, T> pop(const int thread_id = -1) {
        if (thread_id != -1) {
            if (aborted) return {{-2, -1}, T()};
            if (cnt == 0) {
                return {{-1, -1}, T()};
            }
            return _pop();
        } else {
            return _pop();
        }
    }
    int size() {
        return cnt;
    }
    int top() {
        if (cnt == 0) return INF;
        while (cnts[best] == 0) best++;
        return best;
    }
};

struct CLOSE {
    vector<State> states;
    unordered_map<int, int> ids;
    mutex mtx;
    int id(int hash) {
        auto it = ids.find(hash);
        if (it != ids.end()) return it->second;
        return -1;
    }
    void add(int hash, int id) {
        ids[hash] = id;
    }
};

struct Counting_States {
    mutex mtx;
    int cnt;
    Counting_States() : cnt(0) {
    }
    Counting_States& operator++() {
        unique_lock<mutex> lk(mtx);
        ++cnt;
        return *this;
    }
    int count() {
        unique_lock<mutex> lk(mtx);
        return cnt;
    }
};
vector<CLOSE> close_f(hash_distribute_num);
Trie_f trie_f;

struct OPEN_OBAT {
    OPEN_Arrays<pair<int, int>> open_n;
    OPEN_Arrays<pair<int, int>> Deffered;

    map<pair<int, int>, vector<pair<int, pair<int, int>>>> mem;
    vector<unordered_set<int>> open_n_inserted_set;
    mutex mtx;
    OPEN_OBAT() {
        open_n_inserted_set.resize(hash_distribute_num);
    }
    int open_n_top() {
        return open_n.top();
    }
    int Deffered_top() {
        return Deffered.top();
    }
    int open_n_min() {
        return open_n.min();
    }
    pair<int, pair<int, int>> Deffered_pop(int thread_id) {
        return Deffered.pop(thread_id);
    }

    void Deffered_push(int p_h, pair<int, int> p_data,
                       vector<pair<int, pair<int, int>>> data) {
        Deffered.push({p_h, p_data});
        mem[p_data] = data;
    }

    void open_n_push(int h, pair<int, int> data) {
        auto [id, distribution_id] = data;
        if (open_n_inserted_set[distribution_id].count(id)) return;
        open_n_inserted_set[distribution_id].insert(id);
        open_n.push({h, {id, distribution_id}});
    }

    void mv(int thread_id) {
        auto p_data = Deffered_pop(thread_id).second;
        auto it = mem.find(p_data);
        for (auto [h, data] : it->second) {
            open_n_push(h, data);
        }
        mem.erase(it);
    }
};
OPEN_OBAT open;

struct CONTINUE_FLAG {
    bool found_solution;
    int last_state_id_f, last_state_id_b;
    int last_disitribution_id;
    int forward_num;
    int backward_num;
    vector<int> ans_op;
    int ans_cost;
    CONTINUE_FLAG()
        : found_solution(false),
          last_state_id_f(-1),
          last_state_id_b(-1),
          last_disitribution_id(-1) {
    }
    mutex mtx;
    bool found(int f_id, int search_type, int thread_id,
               int hash_distribution) {
        unique_lock<mutex> lk(mtx);
        if (!found_solution) {
            last_state_id_f = f_id;
            if (check_ans(search_type, thread_id, hash_distribution)) {
                found_solution = true;
                return true;
            }
        }
        return false;
    }

    bool operator()() {
        unique_lock<mutex> lk(mtx);
        return found_solution;
    }

    bool check_ans(int search_type, int thread_id, int hash_distibution) {
        ans_cost = 0;
        ans_op.clear();
        forward_num = 0;
        backward_num = 0;
        last_disitribution_id = hash_distibution;
        if (search_type == 0) {
            while (true) {
                close_f[last_disitribution_id].mtx.lock();
                State state =
                    close_f[last_disitribution_id].states[last_state_id_f];
                close_f[last_disitribution_id].mtx.unlock();
                if (state.prev_operator == -1) break;
                ans_cost += action_cost[state.prev_operator];
                ans_op.push_back(state.prev_operator);
                last_state_id_f = state.prev_id;
                last_disitribution_id = state.par_hash_distribution;
                ++forward_num;
            }
            reverse(ans_op.begin(), ans_op.end());
            return ans_check(ans_op);
        }
        return true;
    }
};

CONTINUE_FLAG flg;
Counting_States expanded_states, generated_states, evaluated_states;

struct H_value {
    unordered_map<int, int> mem;
    mutex mtx;
    int h_val(int hash) {
        unique_lock<mutex> lk(mtx);
        auto it = mem.find(hash);
        if (it == mem.end()) return -1;
        return it->second;
    }
    void add(int hash, int h_val) {
        unique_lock<mutex> lk(mtx);
        mem[hash] = h_val;
    }
};
vector<H_value> h_values(hash_distribute_num);

bool Found(int f_id, int search_type, int thread_id,
           int now_hash_distribution) {
    if (flg.found(f_id, search_type, thread_id, now_hash_distribution)) {
        return true;
    }
    return false;
}

void Search(const int thread_id) {
    while (!flg()) {
        if (calculate_time() > time_limit * 0.99) {
            cout << "Time limit has been reached." << endl;
            quick_exit(23);
        }
        open.mtx.lock();
        int open_n_tp = open.open_n_top();
        int Deffered_tp = open.Deffered_top();
        int expanded_min = open.open_n_min();
        if (open_n_tp >= Deffered_tp) {  // if h(top(open))>=h(top(Deffered))
            if (Deffered_tp <= expanded_min) {  // if h(top(Deffered)) <=
                                                // min(h(expanding_state))
                open.mv(thread_id);  // insert succ(top(Deffered)) into open,
                                     // and pop(top(Deffered))
            }
            open.mtx.unlock();
            continue;
        }
        auto [now_h, now_state_id_and_hashdistibution] = open.open_n.pop(
            thread_id);  // if h(top(open))<= min(h(expanding_state)) pop
                         // top(open), else now_h<0
        if (now_h >= 0) {
            open.open_n.mn.insert(now_h);
        }
        open.mtx.unlock();
        if (now_h < 0) continue;
        int now_state_id = now_state_id_and_hashdistibution.first;
        int now_hash_distribution = now_state_id_and_hashdistibution.second;

        close_f[now_hash_distribution].mtx.lock();
        State s = close_f[now_hash_distribution].states[now_state_id];
        close_f[now_hash_distribution].mtx.unlock();
        auto& now_state = s.state;
        ++expanded_states;
        if (GoalCheck(now_state)) {
            if (Found(now_state_id, 0, thread_id, now_hash_distribution)) {
                return;
            }
        }
        vector<int> operatable_id;
        trie_f.search(now_state, operatable_id);
        vector<pair<int, pair<int, int>>> succesor_states;
        int min_h = now_h;

        for (auto i : operatable_id) {
            auto [next_state, next_hash] =
                effect_f(now_state, eff_op_f[i], s.hash);
            int next_distribution_id = next_hash % thread_num;
            ++generated_states;
            int h = h_values[next_distribution_id].h_val(
                next_hash);  // if next_state have been evaluated, using the
                             // cash
            if (h == -1) {
#ifdef FF
                h = H_FF(next_state, goal_pair, goal, thread_id);
#endif
                h_values[next_distribution_id].add(next_hash, h);
                ++evaluated_states;
            }
            if (h < min_h) min_h = h;
            if (h == INF) continue;
            close_f[next_distribution_id].mtx.lock();
            int next_state_id = close_f[next_distribution_id].id(next_hash);
            if (next_state_id == -1) {
                next_state_id = close_f[next_distribution_id].states.size();
                close_f[next_distribution_id].states.emplace_back(
                    next_state, now_state_id, i, next_state_id, next_hash,
                    next_distribution_id, now_hash_distribution);
                close_f[next_distribution_id].add(next_hash, next_state_id);
            }

            close_f[next_distribution_id].mtx.unlock();
            succesor_states.push_back(
                {h, {next_state_id, next_distribution_id}});
        }
        open.mtx.lock();
        if (min_h < now_h) {  // s is a b-state
            open.Deffered_push(now_h, now_state_id_and_hashdistibution,
                               succesor_states);
        } else {  // s is an a-state
            for (auto [h, pair_succ_id_next_distribution_id] :
                 succesor_states) {
                open.open_n_push(h, pair_succ_id_next_distribution_id);
            }
        }
        auto it = open.open_n.mn.find(now_h);
        open.open_n.mn.erase(it);
        open.mtx.unlock();
    }
}

int main() {
    // 入力開始
    clock_gettime(CLOCK_REALTIME, &start_time);

    string filename = "sas_plan";
    int exitcode = input();
    if (exitcode == 34) {
        cout << "Tried to use unsupported feature." << endl;
        return 34;
    }

    build_factacc();
    make_Trie();
    make_HashTable();

#ifdef FF
    g_to_a.resize(n);
    for (int i = 0; i < n; i++) g_to_a[i].resize(variable_range[i]);
    for (int i = 0; i < op; i++) {
        for (auto p : pre_op_pairs[i]) {
            int a = p.first, b = p.second;
            g_to_a[a][b].push_back(i);
        }
    }
    dp_g.resize(thread_num);
    best_supporter_function.resize(thread_num);
    close_ff.resize(thread_num);
    for (int i = 0; i < thread_num; i++) {
        dp_g[i].resize(n);
        best_supporter_function[i].resize(n);
        close_ff[i].resize(n);
        for (int j = 0; j < n; j++) {
            dp_g[i][j].resize(variable_range[j], INF);
            best_supporter_function[i][j].resize(variable_range[j], -1);
            close_ff[i][j].resize(variable_range[j]);
        }
    }
#endif
    /// 初期値
#ifdef GoalCount
    int start_h = H_GoalCount(start, goal_pair);
#endif
#ifdef FF
    int start_h = H_FF(start, goal_pair, goal, 0);
#endif
    ++evaluated_states;
    ++generated_states;
    if (start_h == INF) {
        cout << "Search stopped without finding a solution." << endl;
        return 12;
    }
    int start_hash = calc_hash(start);
    int start_hash_distribution = start_hash % hash_distribute_num;
    h_values[start_hash_distribution].add(start_hash, start_h);
    close_f[start_hash_distribution].add(start_hash, 0);
    close_f[start_hash_distribution].states.emplace_back(
        start, -1, -1, 0, start_hash, start_hash_distribution, -1);
    open.open_n_push(start_h, {0, start_hash_distribution});

    double search_start_time = calculate_time();  // thread
    vector<thread> threads;
    for (int i = 0; i < thread_num; i++) {
        threads.push_back(thread(Search, i));
    }
    for (thread& th : threads) {
        th.join();
    }

    double search_end_time = calculate_time();
    double search_time = search_end_time - search_start_time;

    if (!flg.found_solution) {
        cout << "Search stopped without finding a solution." << endl;
        return 12;
    }

    // 標準出力
    for (int i = 0; i < (int)flg.ans_op.size(); i++) {
        cout << op_name[flg.ans_op[i]] << endl;
    }
    cout << endl;

    write_file(filename);

    double expansion_rate = (double)expanded_states.count() / search_time;

    cout << "Solution found." << endl;
    cout << "Plan cost: " << flg.ans_op.size() << endl;
    cout << "Expanded " << expanded_states.count() << " state(s)." << endl;
    cout << "Evaluated " << evaluated_states.count() << " state(s)." << endl;
    cout << "Generated " << generated_states.count() << " state(s)." << endl;
    cout << "Expansion rate: " << expansion_rate << endl;
    cout << "Search time: " << search_time << "s" << endl;
    cout << "Total time: " << calculate_time() << "s" << endl;
    return 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////

double calculate_time() {
    timespec now_time;
    clock_gettime(CLOCK_REALTIME, &now_time);
    int sec = now_time.tv_sec - start_time.tv_sec;
    int nsec = now_time.tv_nsec - start_time.tv_nsec;
    double d_sec = (double)sec + (double)nsec / (1000 * 1000 * 1000);
    return d_sec;
}

void make_HashTable() {
    Hash_table.resize(n);
    for (int i = 0; i < n; i++) {
        Hash_table[i].resize(variable_range[i] + 1);
        for (int j = 0; j < variable_range[i] + 1; j++) {
            Hash_table[i][j] = rand();
        }
    }
}

int calc_hash(const vector<short>& state) {
    int res = 0;
    for (int i = 0; i < n; i++) {
        res ^= Hash_table[i][state[i] != -1 ? state[i] : variable_range[i]];
    }
    return res;
}

void make_Trie() {
    for (int i = 0; i < op; i++) {
        sort(pre_op_pairs[i].begin(), pre_op_pairs[i].end());
        trie_f.insert(pre_op_pairs[i], i);
    }
    trie_f.build();
}

vector<pair<int, short>> check_mutex(vector<short>& state) {
    queue<pair<int, short>> que;
    vector<pair<int, short>> state_pair;
    for (int i = 0; i < n; i++) {
        if (state[i] != -1) que.emplace(i, state[i]);
    }
    vector<set<int>> mutex_set(n);
    while (!que.empty()) {
        pair<int, short> pr = que.front();
        state_pair.push_back(pr);
        que.pop();
        for (auto v : mutex_map[pr]) {
            if (state[v.first] == v.second) return {make_pair(-1, -1)};
            if (state[v.first] == -1) {
                mutex_set[v.first].insert(v.second);
                if ((int)mutex_set[v.first].size() + 1 ==
                    variable_range[v.first]) {
                    for (int i = 0; i < variable_range[v.first]; i++) {
                        if (!mutex_set[v.first].count(i)) {
                            state[v.first] = i;
                            que.emplace(v.first, i);
                        }
                    }
                }
            }
        }
    }
    return state_pair;
}

void build_factacc() {
    fact_acc.resize(n + 1);
    for (int i = 0; i < n; i++) {
        fact_acc[i + 1] = fact_acc[i] + variable_range[i];
    }
    fact_num = fact_acc.back();
}

set<pair<int, int>> operator_mutex(int& operate_id) {
    set<pair<int, int>> res;
    for (auto [var, value] : pre_op_b[operate_id]) {
        for (auto pr : mutex_map[make_pair(var, value)]) {
            if (eff_op_b[operate_id][pr.first] == -1) res.insert(pr);
        }
    }
    return res;
}

vector<pair<int, short>> make_fact(vector<short>& state) {
    vector<pair<int, short>> res;
    for (int i = 0; i < n; i++) {
        if (state[i] != -1) res.emplace_back(i, state[i]);
    }
    return res;
}

pair<vector<short>, int> effect_f(vector<short> state,
                                  const vector<pair<int, short>>& effect,
                                  int hash = 0) {
    for (int i = 0; i < (int)effect.size(); i++) {
        hash ^= Hash_table[effect[i].first][state[effect[i].first]];
        hash ^= Hash_table[effect[i].first][effect[i].second];
        state[effect[i].first] = effect[i].second;
    }
    return {state, hash};
}

int H_GoalCount(const vector<short>& forward_state,
                const vector<pair<int, short>>& back_state_pair) {
    int unsatisfied_goal_count = 0;
    for (auto p : back_state_pair) {
        if (forward_state[p.first] != p.second) unsatisfied_goal_count++;
    }
    return unsatisfied_goal_count;
}

int H_FF(const vector<short>& forward_state,
         const vector<pair<int, short>>& back_state_pair,
         vector<short>& back_state, const int& thread_id) {
    int cnt = back_state_pair.size();
    vector<int> dp_a(op, 1);
    vector<int> cnt_a(op);
    for (int i = 0; i < op; i++) cnt_a[i] = pre_op_pairs[i].size();

    OPEN_Arrays<pair<int, int>> q;
    vector<pair<int, int>> undo_dp_g;
    vector<pair<int, int>> undo_best_supporter_function;
    vector<pair<int, int>> undo_close_ff;
    for (int i = 0; i < n; i++) {
        dp_g[thread_id][i][forward_state[i]] = 0;
        undo_dp_g.emplace_back(i, forward_state[i]);
        q.push({0, {i, forward_state[i]}});
    }
    for (int i = 0; i < op; i++) {
        if (pre_op_pairs[i].empty()) {
            q.push({1, {i, -1}});
        }
    }
    while (q.cnt) {
        auto [x, p] = q.pop();
        if (p.second != -1) {
            if (dp_g[thread_id][p.first][p.second] != x) continue;
            if (back_state[p.first] == p.second) {
                --cnt;
                if (cnt == 0) {
                    break;
                }
            }
            for (auto to : g_to_a[p.first][p.second]) {
                dp_a[to] += dp_g[thread_id][p.first][p.second];
                --cnt_a[to];
                if (cnt_a[to] == 0) {
                    q.push({dp_a[to], {to, -1}});
                }
            }
        } else {
            for (auto to : eff_op_f[p.first]) {
                if (dp_g[thread_id][to.first][to.second] == INF) {
                    undo_dp_g.emplace_back(to.first, to.second);
                }
                if (dp_g[thread_id][to.first][to.second] > x) {
                    dp_g[thread_id][to.first][to.second] = x;
                    if (best_supporter_function[thread_id][to.first]
                                               [to.second] == -1) {
                        undo_best_supporter_function.emplace_back(to.first,
                                                                  to.second);
                    }
                    best_supporter_function[thread_id][to.first][to.second] =
                        p.first;
                    q.push({x, {to.first, to.second}});
                }
            }
        }
    }
    int res = 0;
    if (!cnt) {
        for (int i = 0; i < n; i++) {
            close_ff[thread_id][i][forward_state[i]] = true;
            undo_close_ff.emplace_back(i, forward_state[i]);
        }
        queue<pair<int, int>> open_ff;
        for (auto p : back_state_pair) {
            if (!close_ff[thread_id][p.first][p.second]) {
                open_ff.emplace(p.first, p.second);
            }
        }
        while (!open_ff.empty()) {
            pair<int, int> g = open_ff.front();
            open_ff.pop();

            close_ff[thread_id][g.first][g.second] = true;
            undo_close_ff.emplace_back(g.first, g.second);
            res++;
            int bs_g = best_supporter_function[thread_id][g.first][g.second];
            for (auto to : pre_op_pairs[bs_g]) {
                if (!close_ff[thread_id][to.first][to.second]) {
                    open_ff.push(to);
                    close_ff[thread_id][to.first][to.second] = true;
                    undo_close_ff.push_back(to);
                }
            }
        }
    } else {
        res = INF;
    }
    for (auto& p : undo_dp_g) dp_g[thread_id][p.first][p.second] = INF;
    for (auto& p : undo_best_supporter_function)
        best_supporter_function[thread_id][p.first][p.second] = -1;
    for (auto& p : undo_close_ff)
        close_ff[thread_id][p.first][p.second] = false;
    return res;
}

bool GoalCheck(const vector<short>& state,
               const vector<pair<int, short>>& back_state_pair) {
    for (auto [i, j] : back_state_pair) {
        if (state[i] != j) return false;
    }
    return true;
}

bool operatable(const vector<short>& state, const int op_id) {
    for (auto p : pre_op_pairs[op_id]) {
        if (state[p.first] != p.second) return false;
    }
    return true;
}

bool ans_check(const vector<int>& ans_op) {
    vector<short> state = start;
    for (auto i : ans_op) {
        if (operatable(state, i)) {
            state = effect_f(state, eff_op_f[i]).first;
        } else {
            return false;
        }
    }
    return GoalCheck(state);
}

int input() {
    string tmp;
    // version section
    cin >> tmp;  // begin_version
    int version;
    cin >> version;
    cin >> tmp;  // end_version

    // metric section
    cin >> tmp;  // begin_metric
    cin >> metric;
    cin >> tmp;  // end_metric

    // variables section
    cin >> n;
    // v.resize(n);
    variable_range.resize(n);
    for (int i = 0; i < n; i++) {
        cin >> tmp;  // begin_variable
        cin >> tmp;  // the name of the variable
        cin >> tmp;  // the axiom layer of the variable
        short r;     // varialbe's range
        cin >> r;
        cin.ignore();
        variable_range[i] = r;
        // v[i].resize(r);
        for (int j = 0; j < r; j++) {
            // getline(cin, v[i][j]);  // the symbolic name
            getline(cin, tmp);
        }
        cin >> tmp;  // end_variable
    }

    // mutex section
    cin >> mutex_num;

    mutex_pair.resize(mutex_num);
    for (int i = 0; i < mutex_num; i++) {
        cin >> tmp;                              // begin_mutex_group
        int number_of_facts_in_the_mutex_group;  // the number of facts in
                                                 // the mutex group
        cin >> number_of_facts_in_the_mutex_group;
        for (int j = 0; j < number_of_facts_in_the_mutex_group; j++) {
            int var;
            short value;
            cin >> var >> value;
            mutex_pair[i].emplace_back(var, value);
        }
        cin >> tmp;  // end_mutex_group
    }
    for (auto pair : mutex_pair) {
        for (auto mutex_key : pair) {
            for (auto imcompatible : pair) {
                if (imcompatible != mutex_key)
                    mutex_map[mutex_key].push_back(imcompatible);
            }
        }
    }

    // initial state section
    cin >> tmp;  // begin_state
    start.resize(n);
    for (int i = 0; i < n; i++) {
        cin >> start[i];
    }
    cin >> tmp;  // end_state

    // goal section
    cin >> tmp;  // begin_goal
    cin >> goal_number;
    goal.assign(n, -1);
    for (int i = 0; i < goal_number; i++) {
        int var;
        short value;
        cin >> var >> value;
        goal[var] = value;
        goal_pair.emplace_back(var, value);
    }
    cin >> tmp;  // end_goal

    cin >> op;
    op_name.resize(op);
    pre_op_f.assign(op, vector<short>(n, -1));
    pre_op_pairs.resize(op);
    eff_op_f.resize(op);
    pre_op_b.resize(op);
    eff_op_b.resize(op, vector<short>(n, -1));
    eff_op_b_pairs.resize(op);
    action_cost.resize(op);
    for (int i = 0; i < op; i++) {
        cin >> tmp;  // begin_operator
        cin.ignore();
        getline(cin, op_name[i]);
        int number_of_prevail_condition;
        cin >> number_of_prevail_condition;
        for (int j = 0; j < number_of_prevail_condition; j++) {
            int pre_variable;
            short pre_value;
            cin >> pre_variable >> pre_value;
            pre_op_f[i][pre_variable] = pre_value;
            pre_op_pairs[i].emplace_back(pre_variable, pre_value);
            pre_op_b[i].emplace_back(pre_variable, pre_value);
            eff_op_b[i][pre_variable] = pre_value;
            eff_op_b_pairs[i].emplace_back(pre_variable, pre_value);
        }
        int number_of_effects;  // the number of effects
        cin >> number_of_effects;
        for (int j = 0; j < number_of_effects; j++) {
            int the_number_of_effect_conditions;  // In STRIPS domains, this
                                                  // will usually be 0
            int the_effected_variable;
            short precondition;
            short new_value;
            cin >> the_number_of_effect_conditions;
            if (the_number_of_effect_conditions > 0) {
                return 34;
            }
            cin >> the_effected_variable >> precondition >> new_value;
            pre_op_f[i][the_effected_variable] = precondition;
            if (precondition != -1) {
                pre_op_pairs[i].emplace_back(the_effected_variable,
                                             precondition);
            }
            eff_op_f[i].emplace_back(the_effected_variable, new_value);
            pre_op_b[i].emplace_back(the_effected_variable, precondition);
            eff_op_b[i][the_effected_variable] = new_value;
            eff_op_b_pairs[i].emplace_back(the_effected_variable, new_value);
        }
        cin >> action_cost[i];
        if (metric == 0) action_cost[i] = 1;
        cin >> tmp;  // end_operator
    }

    cin >> axiom;
    if (axiom != 0) {
        return 34;
    }

    cout << "done reading input!" << endl << endl;
    return 0;
}

void write_file(const string& filename) {
    ofstream writing_file;
    writing_file.open(filename, ios::out);
    for (int i = 0; i < (int)flg.ans_op.size(); i++) {
        writing_file << "(";
        writing_file << op_name[flg.ans_op[i]];
        writing_file << ")" << endl;
    }
    writing_file << "; cost = " << flg.ans_cost;
    if (metric == 0)
        writing_file << " (unit cost)" << endl;
    else
        writing_file << " (general cost)" << endl;
    writing_file.close();
}