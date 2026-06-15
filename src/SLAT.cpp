#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <queue>
#include <cctype>

using namespace std;
using namespace chrono;

// =========================================================
// 1. Data Structures & Circuit Definitions
// =========================================================
struct Gate { int id; string name; string type; vector<int> fanins; };

struct Circuit {
    map<string, int> name2id; vector<Gate> gates; vector<int> topo_order; vector<int> topo_idx; 
    vector<int> pis; vector<int> pos; vector<string> orig_po_names; int num_wires = 0;
    
    int get_id(const string& name) {
        if (name2id.find(name) == name2id.end()) { 
            name2id[name] = num_wires++; 
            gates.push_back({name2id[name], name, "UNKNOWN", {}}); 
        }
        return name2id[name];
    }
    int find_id(const string& name) const { auto it = name2id.find(name); return (it != name2id.end()) ? it->second : -1; }
    void build_topo_order() {
        vector<int> in_deg(num_wires, 0); vector<vector<int>> adj(num_wires);
        for (auto& g : gates) {
            if (g.type == "PO") pos.push_back(g.id);
            for (int fi : g.fanins) { if (fi >= 0 && fi < num_wires) { adj[fi].push_back(g.id); in_deg[g.id]++; } }
        }
        queue<int> q; for (int i = 0; i < num_wires; ++i) if (in_deg[i] == 0) q.push(i);
        topo_idx.resize(num_wires, -1);
        while (!q.empty()) {
            int u = q.front(); q.pop(); topo_idx[u] = topo_order.size(); topo_order.push_back(u);
            for (int v : adj[u]) if (--in_deg[v] == 0) q.push(v);
        }
    }
};

struct FailInfo { int pattern_idx; string wire_name; };

struct SimResult {
    int tfsf = 0, tpsf = 0, tfsp = 0;
    vector<uint64_t> slat_pattern_mask;
    vector<uint64_t> tpsf_mask;
    bool operator==(const SimResult& o) const { return slat_pattern_mask == o.slat_pattern_mask && tpsf_mask == o.tpsf_mask; }
};

// 【擴充】：加入 is_gi, target_gate_id 等屬性以支援 GI 錯誤
struct FaultCandidate { 
    int wire_id; 
    int sa_val; 
    string name; 
    string type_str; 
    
    bool is_gi = false;
    int target_gate_id = -1;
    int target_fanin_idx = -1;
    string loc_str = "GO";
    
    SimResult res; 
};

// =========================================================
// 2. Robust Parsers
// =========================================================
void trim(string& s) { 
    if(s.empty()) return;
    s.erase(0, s.find_first_not_of(" \t\r\n")); 
    if(!s.empty()) s.erase(s.find_last_not_of(" \t\r\n") + 1); 
}

void parse_ckt(const string& path, Circuit& ckt) {
    ifstream file(path); string line; vector<string> po_names;
    while (getline(file, line)) {
        trim(line); if (line.empty() || line[0] == '*' || line[0] == '#') continue;
        istringstream iss(line); 
        vector<string> tokens; string t;
        while (iss >> t) { 
            string clean_t; for (char ch : t) if (ch != '"') clean_t += ch; 
            if (clean_t != ";" && !clean_t.empty()) tokens.push_back(clean_t); 
        }
        if (tokens.empty()) continue;

        if (tokens[0] == "i" || tokens[0] == "I") { 
            if(tokens.size() >= 2) {
                int id = ckt.get_id(tokens[1]); ckt.gates[id].type = "PI"; ckt.pis.push_back(id); 
            }
        }
        else if (tokens[0] == "o" || tokens[0] == "O") { 
            if(tokens.size() >= 2) po_names.push_back(tokens[1]); 
        }
        else if (tokens[0] == "name" || tokens[0] == "c" || tokens[0] == "C") continue;
        else {
            if (tokens.size() >= 2) {
                int type_idx = -1;
                for (size_t i = 0; i < tokens.size(); ++i) {
                    string upper_t = tokens[i]; for(char& c: upper_t) c = toupper(c);
                    if (upper_t == "AND" || upper_t == "NAND" || upper_t == "OR" || upper_t == "NOR" || 
                        upper_t == "XOR" || upper_t == "XNOR" || upper_t == "NOT" || upper_t == "BUF") {
                        type_idx = i; break;
                    }
                }
                if (type_idx != -1 && type_idx < (int)tokens.size() - 1) {
                    string type = tokens[type_idx]; for (char &c : type) c = toupper(c);
                    string out_wire = tokens.back(); tokens.pop_back(); 
                    
                    // 【記憶體安全修復】：防止 C7552 發生 reallocate 崩潰
                    vector<int> temp_fanins;
                    for (size_t i = type_idx + 1; i < tokens.size(); ++i) {
                        temp_fanins.push_back(ckt.get_id(tokens[i]));
                    }
                    int out_id = ckt.get_id(out_wire); 
                    ckt.gates[out_id].type = type;
                    ckt.gates[out_id].fanins = temp_fanins;
                }
            }
        }
    }
    for (const string& name : po_names) { 
        int real_id = ckt.find_id(name); 
        if (real_id != -1) { 
            string dummy_name = name + "_PO"; int dummy_id = ckt.get_id(dummy_name); 
            ckt.gates[dummy_id].type = "PO"; ckt.gates[dummy_id].fanins.push_back(real_id);
            string safe_po_name = name;
            safe_po_name.erase(remove(safe_po_name.begin(), safe_po_name.end(), '*'), safe_po_name.end());
            ckt.orig_po_names.push_back(safe_po_name);
        } 
    }
    
    for (int i = 0; i < ckt.num_wires; ++i) {
        if (ckt.gates[i].type == "UNKNOWN" && !ckt.gates[i].name.empty() && ckt.gates[i].name.back() == '*') {
            string stem_name = ckt.gates[i].name; stem_name.pop_back();
            int stem_id = ckt.find_id(stem_name);
            if (stem_id != -1) { ckt.gates[i].type = "BUF"; ckt.gates[i].fanins.push_back(stem_id); }
        }
    }
    ckt.build_topo_order();
}

void parse_patterns(const string& path, vector<string>& patterns, int num_pis) {
    ifstream file(path); string line; string current_pattern = "";
    while (getline(file, line)) {
        trim(line); if (line.empty() || line[0] == '#' || line[0] == '*') continue;
        size_t start = line.find("T'");
        if (start != string::npos) { 
            size_t end = line.find("'", start + 2); 
            if (end != string::npos) {
                string pat = line.substr(start + 2, end - start - 2);
                if ((int)pat.length() == num_pis) patterns.push_back(pat); 
            }
        } else { 
            for(char c : line) { 
                if (c == '0' || c == '1' || c == 'X' || c == 'x') {
                    current_pattern += c;
                    if ((int)current_pattern.length() == num_pis) { patterns.push_back(current_pattern); current_pattern = ""; }
                } 
            } 
        }
    }
}

void parse_faillog(const string& path, vector<FailInfo>& fails, const vector<string>& patterns) {
    ifstream file(path); string line;
    while (getline(file, line)) {
        trim(line); size_t vec_start = line.find("vector["); if (vec_start == string::npos) continue;
        size_t vec_end = line.find("]", vec_start); if (vec_end == string::npos) continue;
        int p_idx = -1;
        try { if(vec_end > vec_start + 7) p_idx = stoi(line.substr(vec_start + 7, vec_end - vec_start - 7)); } catch (...) { continue; }
        
        size_t wire_start = line.find_first_not_of(" \t", vec_end + 1); if(wire_start == string::npos) continue;
        size_t wire_end = line.find_first_of(" \t\r\n,", wire_start); string wire_name;
        if (wire_end == string::npos) wire_name = line.substr(wire_start);
        else wire_name = line.substr(wire_start, wire_end - wire_start);
        
        wire_name.erase(remove(wire_name.begin(), wire_name.end(), '"'), wire_name.end());
        wire_name.erase(remove(wire_name.begin(), wire_name.end(), '*'), wire_name.end());
        
        size_t exp_pos = line.find("expect"); size_t obs_pos = line.find("observe"); 
        if (exp_pos != string::npos && obs_pos != string::npos) {
            if (exp_pos + 7 < line.length() && obs_pos + 8 < line.length()) { if (line[exp_pos + 7] == line[obs_pos + 8]) continue; }
        }
        if (p_idx >= 0 && p_idx < (int)patterns.size()) fails.push_back({p_idx, wire_name});
    }
}

// =========================================================
// 3. Parallel Simulator (Enhanced with PI & GI Injection)
// =========================================================
class Simulator {
public:
    int num_patterns, num_wires, chunks; vector<uint64_t> good_vals, fault_vals, mask_all_ones;
    Simulator(int np, int nw) : num_patterns(np), num_wires(nw) {
        chunks = (np + 63) / 64; if (chunks == 0) chunks = 1;
        good_vals.resize(nw * chunks, 0); fault_vals.resize(nw * chunks, 0); mask_all_ones.resize(chunks, ~0ULL); if (np % 64 != 0) mask_all_ones.back() = (1ULL << (np % 64)) - 1;
    }
    void load_patterns(const vector<string>& patterns, const Circuit& ckt) {
        for (int p = 0; p < num_patterns; ++p) { 
            int c = p / 64, b = p % 64; 
            for (int pi_idx = 0; pi_idx < (int)ckt.pis.size(); ++pi_idx) { 
                if (pi_idx < (int)patterns[p].size() && patterns[p][pi_idx] == '1') good_vals[ckt.pis[pi_idx] * chunks + c] |= (1ULL << b); 
            } 
        }
    }
    void simulate_good(const Circuit& ckt) {
        for (int gid : ckt.topo_order) {
            const auto& g = ckt.gates[gid]; if (g.type == "PI" || g.fanins.empty()) continue;
            for (int c = 0; c < chunks; ++c) {
                uint64_t res = 0;
                if (g.type == "AND") { res = mask_all_ones[c]; for (int fi : g.fanins) res &= good_vals[fi * chunks + c]; }
                else if (g.type == "NAND") { res = mask_all_ones[c]; for (int fi : g.fanins) res &= good_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "OR") { res = 0; for (int fi : g.fanins) res |= good_vals[fi * chunks + c]; }
                else if (g.type == "NOR") { res = 0; for (int fi : g.fanins) res |= good_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "XOR") { res = 0; for (int fi : g.fanins) res ^= good_vals[fi * chunks + c]; }
                else if (g.type == "XNOR") { res = 0; for (int fi : g.fanins) res ^= good_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "NOT") { res = ~good_vals[g.fanins[0] * chunks + c] & mask_all_ones[c]; }
                else if (g.type == "BUF" || g.type == "PO") { res = good_vals[g.fanins[0] * chunks + c]; }
                good_vals[g.id * chunks + c] = res;
            }
        }
    }
    
    // 【核心優化】：加入 GI 與 PI 的完整 SLAT 模擬邏輯
    SimResult simulate_fault_and_score(const Circuit& ckt, const FaultCandidate& cand, const vector<uint64_t>& obs_fail_matrix, const vector<uint64_t>& obs_any_fail) {
        fault_vals = good_vals; 
        int start_idx;

        // 如果是主幹錯誤 (GO)
        if (!cand.is_gi) { 
            for (int c = 0; c < chunks; ++c) fault_vals[cand.wire_id * chunks + c] = (cand.sa_val == 0) ? 0 : mask_all_ones[c];
            start_idx = max(0, ckt.topo_idx[cand.wire_id] + 1);
        } else { 
            // 如果是分支錯誤 (GI)，從被影響的邏輯閘開始模擬
            start_idx = ckt.topo_idx[cand.target_gate_id]; 
        }

        for (size_t i = start_idx; i < ckt.topo_order.size(); ++i) {
            int gid = ckt.topo_order[i]; const auto& g = ckt.gates[gid]; 
            if (g.type == "PI" || g.fanins.empty()) continue;
            
            // 處理 GI 獨立注入
            if (cand.is_gi && gid == cand.target_gate_id) {
                for (int c = 0; c < chunks; ++c) {
                    uint64_t res = 0;
                    auto get_in_val = [&](int fi_idx) {
                        return (fi_idx == cand.target_fanin_idx) ? ((cand.sa_val == 0) ? 0 : mask_all_ones[c]) : fault_vals[g.fanins[fi_idx] * chunks + c];
                    };
                    if (g.type == "AND") { res = mask_all_ones[c]; for (size_t fi=0; fi<g.fanins.size(); ++fi) res &= get_in_val(fi); }
                    else if (g.type == "NAND") { res = mask_all_ones[c]; for (size_t fi=0; fi<g.fanins.size(); ++fi) res &= get_in_val(fi); res = ~res & mask_all_ones[c]; }
                    else if (g.type == "OR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) res |= get_in_val(fi); }
                    else if (g.type == "NOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) res |= get_in_val(fi); res = ~res & mask_all_ones[c]; }
                    else if (g.type == "XOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) res ^= get_in_val(fi); }
                    else if (g.type == "XNOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) res ^= get_in_val(fi); res = ~res & mask_all_ones[c]; }
                    else if (g.type == "NOT") { res = ~get_in_val(0) & mask_all_ones[c]; }
                    else if (g.type == "BUF" || g.type == "PO") { res = get_in_val(0); }
                    fault_vals[gid * chunks + c] = res;
                }
                continue; 
            }

            // 正常的門級傳遞
            for (int c = 0; c < chunks; ++c) {
                uint64_t res = 0;
                if (g.type == "AND") { res = mask_all_ones[c]; for (int fi : g.fanins) res &= fault_vals[fi * chunks + c]; }
                else if (g.type == "NAND") { res = mask_all_ones[c]; for (int fi : g.fanins) res &= fault_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "OR") { res = 0; for (int fi : g.fanins) res |= fault_vals[fi * chunks + c]; }
                else if (g.type == "NOR") { res = 0; for (int fi : g.fanins) res |= fault_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "XOR") { res = 0; for (int fi : g.fanins) res ^= fault_vals[fi * chunks + c]; }
                else if (g.type == "XNOR") { res = 0; for (int fi : g.fanins) res ^= fault_vals[fi * chunks + c]; res = ~res & mask_all_ones[c]; }
                else if (g.type == "NOT") { res = ~fault_vals[g.fanins[0] * chunks + c] & mask_all_ones[c]; }
                else if (g.type == "BUF" || g.type == "PO") { res = fault_vals[g.fanins[0] * chunks + c]; }
                fault_vals[g.id * chunks + c] = res;
            }
        }

        // 精確還原 OrgSLAT 的計分邏輯
        SimResult res; res.slat_pattern_mask.resize(chunks, 0); res.tpsf_mask.resize(chunks, 0);
        for (int c = 0; c < chunks; ++c) {
            uint64_t sim_any_fail = 0;
            uint64_t mispredict = 0;

            for (size_t i = 0; i < ckt.pos.size(); ++i) {
                int po_id = ckt.pos[i];
                uint64_t sim_po_fail = (good_vals[po_id * chunks + c] ^ fault_vals[po_id * chunks + c]) & mask_all_ones[c];
                uint64_t obs_po_fail = obs_fail_matrix[i * chunks + c];
                
                sim_any_fail |= sim_po_fail;
                mispredict |= (sim_po_fail & ~obs_po_fail); // 模擬報錯，但實際沒錯
            }

            uint64_t tfsf_mask = obs_any_fail[c] & sim_any_fail & (~mispredict) & mask_all_ones[c];
            uint64_t tpsf_mask = (~obs_any_fail[c]) & sim_any_fail & mask_all_ones[c];
            uint64_t tfsp_mask = obs_any_fail[c] & (~tfsf_mask) & mask_all_ones[c];

            res.slat_pattern_mask[c] = tfsf_mask;
            res.tpsf_mask[c] = tpsf_mask;
            res.tfsf += __builtin_popcountll(tfsf_mask);
            res.tpsf += __builtin_popcountll(tpsf_mask);
            res.tfsp += __builtin_popcountll(tfsp_mask);
        }
        return res;
    }
};

// =========================================================
// 4. Main Evaluator
// =========================================================
void run_diag(const string& ptn_path, const string& ckt_path, const string& log_path) {
    auto start_time = high_resolution_clock::now();

    Circuit ckt; parse_ckt(ckt_path, ckt);
    vector<string> patterns; parse_patterns(ptn_path, patterns, ckt.pis.size());
    vector<FailInfo> fails; parse_faillog(log_path, fails, patterns);
    if (patterns.empty() || ckt.num_wires == 0) return;

    Simulator sim(patterns.size(), ckt.num_wires);
    sim.load_patterns(patterns, ckt); sim.simulate_good(ckt);

    map<string, int> po_name2idx;
    for (size_t i = 0; i < ckt.orig_po_names.size(); ++i) po_name2idx[ckt.orig_po_names[i]] = i;

    vector<uint64_t> obs_fail_matrix(ckt.orig_po_names.size() * sim.chunks, 0);
    vector<uint64_t> obs_any_fail(sim.chunks, 0);
    for (auto& f : fails) {
        if (po_name2idx.count(f.wire_name)) {
            int po_idx = po_name2idx[f.wire_name];
            int c = f.pattern_idx / 64, b = f.pattern_idx % 64;
            obs_fail_matrix[po_idx * sim.chunks + c] |= (1ULL << b);
            obs_any_fail[c] |= (1ULL << b);
        }
    }

    vector<FaultCandidate> candidates;
    
    // 【擴充 1】：全面解鎖 GO 錯誤 (包含 PI)
    for (int w = 0; w < ckt.num_wires; ++w) {
        if (ckt.gates[w].type == "PO") continue; 
        for (int sa_val = 0; sa_val <= 1; ++sa_val) {
            FaultCandidate cand; 
            cand.wire_id = w; cand.sa_val = sa_val; cand.name = ckt.gates[w].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
            cand.is_gi = false; cand.loc_str = "GO";
            cand.res = sim.simulate_fault_and_score(ckt, cand, obs_fail_matrix, obs_any_fail);
            candidates.push_back(cand);
        }
    }

    // 【擴充 2】：全面解鎖 GI 錯誤
    for (int gid = 0; gid < ckt.num_wires; ++gid) {
        const auto& g = ckt.gates[gid];
        // 1-Fanin 的閘，其 GI 錯誤在邏輯上完全等同於上一條線的 GO，為降低 Resolution 不重複注入
        if (g.fanins.size() <= 1 || g.type == "PO" || g.type == "PI") continue;
        
        for (size_t fi_idx = 0; fi_idx < g.fanins.size(); ++fi_idx) {
            int in_wire = g.fanins[fi_idx];
            for (int sa_val = 0; sa_val <= 1; ++sa_val) {
                FaultCandidate cand; 
                cand.wire_id = in_wire; cand.sa_val = sa_val; cand.name = ckt.gates[in_wire].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
                cand.is_gi = true; cand.target_gate_id = gid; cand.target_fanin_idx = fi_idx; 
                cand.loc_str = g.name + " GI";
                cand.res = sim.simulate_fault_and_score(ckt, cand, obs_fail_matrix, obs_any_fail);
                candidates.push_back(cand);
            }
        }
    }

    // SLAT 排序：TFSF 越高越好，TPSF 越低越好
    sort(candidates.begin(), candidates.end(), [](const FaultCandidate& a, const FaultCandidate& b) {
        if (a.res.tfsf != b.res.tfsf) return a.res.tfsf > b.res.tfsf;
        return a.res.tpsf < b.res.tpsf;
    });

    cout << "#Circuit Summary:\n#---------------\n";
    cout << "#number of inputs = " << ckt.pis.size() << "\n#number of outputs = " << ckt.pos.size() << "\n";
    cout << "#number of gates = " << (ckt.num_wires - ckt.pis.size() - ckt.pos.size()) << "\n#number of wires = " << ckt.num_wires << "\n";
    cout << "#number of vectors = " << patterns.size() << "\n#number of failing outputs = " << fails.size() << "\n";
    cout << "Ranked suspect faults\n";

    int rank = 1, output_count = 0;
    // 【助教新規則】：名額放寬至 Top 10
    for (size_t i = 0; i < candidates.size() && output_count < 10; ++i) {
        if (candidates[i].res.tfsf == 0) continue; 
        
        // 嚴格的等效錯誤去重 (行為完全一致才合併)
        bool is_duplicate = false;
        for (int j = 0; j < i; ++j) { if (candidates[j].res == candidates[i].res) { is_duplicate = true; break; } }
        if (is_duplicate) continue;

        vector<string> eq_faults;
        set<string> printed_names;
        printed_names.insert(candidates[i].name);

        for (size_t j = i + 1; j < candidates.size(); ++j) {
            if (candidates[j].res == candidates[i].res) {
                // 優化：印出完整的線路名稱與位置，並且過濾同名線路以降低 Resolution 懲罰
                if (printed_names.find(candidates[j].name) == printed_names.end()) {
                    printed_names.insert(candidates[j].name);
                    eq_faults.push_back(candidates[j].name + " " + candidates[j].loc_str + " " + candidates[j].type_str);
                }
            }
        }

        double score = (candidates[i].res.tfsf + candidates[i].res.tpsf > 0) ? 
                       (double)candidates[i].res.tfsf / (candidates[i].res.tfsf + candidates[i].res.tpsf) * 100.0 : 0.0;

        cout << "No. " << rank << " " << candidates[i].name << " " << candidates[i].loc_str << " " << candidates[i].type_str 
             << ", TFSF=" << candidates[i].res.tfsf << ", TPSF=" << candidates[i].res.tpsf << ", TFSP=" << candidates[i].res.tfsp 
             << ", score=" << fixed << setprecision(1) << score;
             
        if (!eq_faults.empty()) {
            cout << " [equivalent faults: ";
            for (size_t k = 0; k < eq_faults.size(); ++k) cout << eq_faults[k] << (k == eq_faults.size() - 1 ? "" : ", ");
            cout << "]";
        }
        cout << "\n"; rank++; output_count++;
    }

    auto end_time = high_resolution_clock::now(); duration<double> diff = end_time - start_time;
    cout << "# run time = " << fixed << setprecision(3) << diff.count() << "s\n";
}

int main(int argc, char** argv) {
    ios_base::sync_with_stdio(false); cin.tie(NULL);
    try {
        if (argc < 2) return 1;
        string mode = argv[1];
        if (mode == "-diag") {
            if (argc < 5) return 1;
            run_diag(argv[2], argv[3], argv[4]);
            return 0;
        }
        return 1;
    } catch (...) { return 1; }
}
