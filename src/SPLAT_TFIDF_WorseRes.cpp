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
#include <cstring>
#include <unordered_map>
#include <unordered_set>
#include <cmath>
using namespace std;
using namespace chrono;

// =========================================================
// 1. Data Structures & Circuit Definitions
// =========================================================
struct Gate {
    int id; string name; string type; vector<int> fanins; vector<string> inputs_raw;
};
struct Circuit {
    unordered_map<string, int> name2id;
    vector<Gate> gates;
    vector<int> topo_order;
    vector<int> topo_idx;
    vector<int> pis;
    vector<int> pos;
    vector<string> orig_po_names;
    vector<string> inputs_raw;
    int num_wires = 0;
    int get_id(const string& name) {
        if (name2id.find(name) == name2id.end()) {
            name2id[name] = num_wires++; gates.push_back({name2id[name], name, "UNKNOWN", {}, {}});
        }
        return name2id[name];
    }
    int find_id(const string& name) const {
        auto it = name2id.find(name); return (it != name2id.end()) ? it->second : -1;
    }
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
struct FaultCandidate {
    int wire_id; int sa_val; string name; string type_str;
    bool is_gi = false; int target_gate_id = -1; int target_fanin_idx = -1; string loc_str = "GO";
    int tfsf = 0, tpsf = 0, tfsp = 0; uint64_t sig_hash = 0; double init_iou = 0.0;
};
struct FaultGroup {
    FaultCandidate rep;
    vector<FaultCandidate> equivs;
};
struct BeamState {
    vector<int> combo;
    int tfsf = 0, tpsf = 0, tfsp = 0;
    double iou = 0.0;
};

// =========================================================
// 2. Robust Parsers
// =========================================================
void trim(string& s) {
    if(s.empty()) return;
    s.erase(0, s.find_first_not_of(" \t\r\n"));
    if(!s.empty()) s.erase(s.find_last_not_of(" \t\r\n") + 1);
}
string normalize_wire(const string &token) {
    string out = token;
    while (!out.empty() && out.back() == '*') out.pop_back();
    return out;
}
void parse_ckt(const string& path, Circuit& ckt) {
    ifstream file(path); string line; vector<string> po_names;
    while (getline(file, line)) {
        trim(line); if (line.empty() || line[0] == '*' || line[0] == '#') continue;
        istringstream iss(line); vector<string> tokens; string t;
        while (iss >> t) {
            string clean_t; for (char ch : t) if (ch != '"') clean_t += ch;
            if (clean_t != ";" && !clean_t.empty()) tokens.push_back(clean_t);
        }
        if (tokens.empty()) continue;
        if (tokens[0] == "i" || tokens[0] == "I") {
            if(tokens.size() >= 2) {
                int id = ckt.get_id(tokens[1]); ckt.gates[id].type = "PI"; ckt.pis.push_back(id); ckt.inputs_raw.push_back(tokens[1]);
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
                        upper_t == "XOR" || upper_t == "XNOR" || upper_t == "NOT" || upper_t == "BUF") { type_idx = i; break; }
                }
                if (type_idx != -1 && type_idx < (int)tokens.size() - 1) {
                    string type = tokens[type_idx]; for (char &c : type) c = toupper(c);
                    string out_wire = tokens.back(); tokens.pop_back();
                    int out_id = ckt.get_id(out_wire); ckt.gates[out_id].type = type;
                    vector<int> temp_fanins; vector<string> temp_inputs_raw;
                    for (size_t i = type_idx + 1; i < tokens.size(); ++i) {
                        temp_fanins.push_back(ckt.get_id(tokens[i]));
                        temp_inputs_raw.push_back(tokens[i]);
                    }
                    out_id = ckt.get_id(out_wire);
                    ckt.gates[out_id].fanins = temp_fanins;
                    ckt.gates[out_id].inputs_raw = temp_inputs_raw;
                }
            }
        }
    }
    for (const string& name : po_names) {
        int real_id = ckt.find_id(name);
        if (real_id != -1) {
            int dummy_id = ckt.get_id(name + "_PO"); ckt.gates[dummy_id].type = "PO"; ckt.gates[dummy_id].fanins.push_back(real_id);
            string safe_po_name = name; safe_po_name.erase(remove(safe_po_name.begin(), safe_po_name.end(), '*'), safe_po_name.end());
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
    ifstream file(path); string line;
    while (getline(file, line)) {
        trim(line);
        if (line.empty() || line[0] == '#' || line[0] == '*') continue;
        size_t start = line.find("T'");
        if (start != string::npos) {
            size_t end = line.find("'", start + 2);
            if (end != string::npos) {
                string pat = line.substr(start + 2, end - start - 2);
                if ((int)pat.length() < num_pis) pat.append(num_pis - pat.length(), '0');
                else if ((int)pat.length() > num_pis) pat = pat.substr(0, num_pis);
                patterns.push_back(pat);
            }
        }
    }
}
void parse_faillog(const string& path, vector<FailInfo>& fails, const vector<string>& patterns) {
    ifstream file(path); string line;
    while (getline(file, line)) {
        trim(line);
        size_t vec_start = line.find("vector["); if (vec_start == string::npos) continue;
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
            if (exp_pos + 7 < line.length() && obs_pos + 8 < line.length()) {
                if (line[exp_pos + 7] == line[obs_pos + 8]) continue;
            }
        }
        if (p_idx >= 0 && p_idx < (int)patterns.size()) fails.push_back({p_idx, wire_name});
    }
}

// =========================================================
// 3. Hyper-Optimized Parallel Simulator (Zero-Overhead)
// =========================================================
class Simulator {
public:
    int num_patterns, num_wires, chunks; 
    vector<uint64_t> good_vals, fault_vals, mask_all_ones;
    
    // 使用原生陣列取代 unordered_map，徹底消滅 Cache Miss
    vector<bool> has_go_fault;
    vector<uint64_t> go_mask;
    vector<int> gi_override_fanin;
    vector<uint64_t> gi_override_val;

    Simulator(int np, int nw) : num_patterns(np), num_wires(nw) {
        chunks = (np + 63) / 64; if (chunks == 0) chunks = 1;
        good_vals.resize(nw * chunks, 0); fault_vals.resize(nw * chunks, 0); 
        mask_all_ones.resize(chunks, ~0ULL); if (np % 64 != 0) mask_all_ones.back() = (1ULL << (np % 64)) - 1;
        
        has_go_fault.resize(nw, false);
        go_mask.resize(nw, 0);
        gi_override_fanin.resize(nw, -1);
        gi_override_val.resize(nw, 0);
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
    
    void simulate_multi(const Circuit& ckt, const vector<int>& combo_indices, const vector<FaultGroup>& groups, const vector<uint64_t>& obs_fail_matrix, int& out_tfsf, int& out_tpsf, int& out_tfsp, double& out_iou, uint64_t* out_sig = nullptr) {
        fault_vals = good_vals; 
        
        // Dirty List 機制，只記錄修改點，模擬後 O(K) 恢復
        vector<int> dirty_wires;
        vector<int> dirty_gates;
        int start_idx = ckt.topo_order.size();
        
        for(int idx : combo_indices) {
            const auto& f = groups[idx].rep;
            if (!f.is_gi) {
                has_go_fault[f.wire_id] = true;
                go_mask[f.wire_id] = (f.sa_val == 1) ? ~0ULL : 0ULL;
                dirty_wires.push_back(f.wire_id);
                start_idx = min(start_idx, max(0, ckt.topo_idx[f.wire_id]));
            } else {
                gi_override_fanin[f.target_gate_id] = f.target_fanin_idx;
                gi_override_val[f.target_gate_id] = (f.sa_val == 1) ? ~0ULL : 0ULL;
                dirty_gates.push_back(f.target_gate_id);
                start_idx = min(start_idx, max(0, ckt.topo_idx[f.target_gate_id]));
            }
        }

        for (size_t i = start_idx; i < ckt.topo_order.size(); ++i) {
            int gid = ckt.topo_order[i]; const auto& g = ckt.gates[gid];
            if (has_go_fault[gid]) {
                for(int c=0; c<chunks; ++c) fault_vals[gid*chunks+c] = go_mask[gid] & mask_all_ones[c];
                continue;
            }
            if (g.type == "PI") continue;

            int ov_fanin = gi_override_fanin[gid];
            for (int c = 0; c < chunks; ++c) {
                uint64_t res = 0;
                if (g.type == "AND") { res = mask_all_ones[c]; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res &= v; } }
                else if (g.type == "NAND") { res = mask_all_ones[c]; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res &= v; } res = ~res & mask_all_ones[c]; }
                else if (g.type == "OR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res |= v; } }
                else if (g.type == "NOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res |= v; } res = ~res & mask_all_ones[c]; }
                else if (g.type == "XOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res ^= v; } }
                else if (g.type == "XNOR") { res = 0; for (size_t fi=0; fi<g.fanins.size(); ++fi) { uint64_t v = ((int)fi == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[fi] * chunks + c]; res ^= v; } res = ~res & mask_all_ones[c]; }
                else if (g.type == "NOT") { uint64_t v = (0 == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[0] * chunks + c]; res = ~v & mask_all_ones[c]; }
                else if (g.type == "BUF" || g.type == "PO") { uint64_t v = (0 == ov_fanin) ? gi_override_val[gid] : fault_vals[g.fanins[0] * chunks + c]; res = v; }
                fault_vals[gid * chunks + c] = res;
            }
        }
        
        out_tfsf = 0; out_tpsf = 0; out_tfsp = 0;
        uint64_t hash_val = 0;
        for (int c = 0; c < chunks; ++c) {
            for (size_t i = 0; i < ckt.pos.size(); ++i) {
                int po_id = ckt.pos[i];
                uint64_t sim_po_fail = (good_vals[po_id * chunks + c] ^ fault_vals[po_id * chunks + c]) & mask_all_ones[c];
                uint64_t obs_po_fail = obs_fail_matrix[i * chunks + c];
                out_tfsf += __builtin_popcountll(sim_po_fail & obs_po_fail);
                out_tpsf += __builtin_popcountll(sim_po_fail & ~obs_po_fail);
                out_tfsp += __builtin_popcountll(~sim_po_fail & obs_po_fail);
                if (out_sig) hash_val ^= sim_po_fail + 0x9e3779b9 + (hash_val << 6) + (hash_val >> 2);
            }
        }
        out_iou = (double)out_tfsf / (out_tfsf + out_tpsf + out_tfsp + 1e-9);
        if (out_sig) *out_sig = hash_val;

        // O(K) 極速恢復狀態
        for(int w : dirty_wires) has_go_fault[w] = false;
        for(int g : dirty_gates) gi_override_fanin[g] = -1;
    }
};

// =========================================================
// 4. High-Accuracy Beam Search Engine
// =========================================================
void run_diag(const string& ptn_path, const string& ckt_path, const string& log_path) {
    auto start_time = high_resolution_clock::now();
    Circuit ckt; parse_ckt(ckt_path, ckt);
    vector<string> patterns; parse_patterns(ptn_path, patterns, ckt.pis.size());
    vector<FailInfo> fails; parse_faillog(log_path, fails, patterns);
    if (patterns.empty() || ckt.num_wires == 0) return;
    Simulator sim(patterns.size(), ckt.num_wires);
    sim.load_patterns(patterns, ckt); sim.simulate_good(ckt);
    unordered_map<string, int> po_name2idx;
    for (size_t i = 0; i < ckt.orig_po_names.size(); ++i) po_name2idx[ckt.orig_po_names[i]] = i;
    vector<uint64_t> obs_fail_matrix(ckt.orig_po_names.size() * sim.chunks, 0);
    vector<bool> po_ever_failed(ckt.pos.size(), false);
    for (auto& f : fails) {
        if (po_name2idx.count(f.wire_name)) {
            int po_idx = po_name2idx[f.wire_name];
            int c = f.pattern_idx / 64, b = f.pattern_idx % 64;
            obs_fail_matrix[po_idx * sim.chunks + c] |= (1ULL << b);
            po_ever_failed[po_idx] = true;
        }
    }
    vector<bool> in_fail_cone(ckt.num_wires, false);
    queue<int> q;
    for (size_t i = 0; i < ckt.pos.size(); ++i) {
        if (po_ever_failed[i]) { in_fail_cone[ckt.pos[i]] = true; q.push(ckt.pos[i]); }
    }
    vector<vector<int>> rev_adj(ckt.num_wires);
    for (int i = 0; i < ckt.num_wires; ++i) { for (int fi : ckt.gates[i].fanins) rev_adj[i].push_back(fi); }
    while(!q.empty()) {
        int u = q.front(); q.pop();
        for (int fi : rev_adj[u]) { if (!in_fail_cone[fi]) { in_fail_cone[fi] = true; q.push(fi); } }
    }
    vector<FaultCandidate> raw_candidates;
    for (int w = 0; w < ckt.num_wires; ++w) {
        if (ckt.gates[w].type == "PO") continue;
        if (!in_fail_cone[w]) continue;
        for (int sa_val = 0; sa_val <= 1; ++sa_val) {
            FaultCandidate cand; cand.wire_id = w; cand.sa_val = sa_val; cand.name = ckt.gates[w].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
            cand.is_gi = false; cand.loc_str = "GO";
            raw_candidates.push_back(cand);
        }
    }
    for (int gid = 0; gid < ckt.num_wires; ++gid) {
        const auto& g = ckt.gates[gid];
        if (g.fanins.size() <= 1 || g.type == "PO" || g.type == "PI") continue;
        if (!in_fail_cone[gid]) continue;
        for (size_t fi_idx = 0; fi_idx < g.fanins.size(); ++fi_idx) {
            int in_wire = g.fanins[fi_idx];
            for (int sa_val = 0; sa_val <= 1; ++sa_val) {
                FaultCandidate cand; cand.wire_id = in_wire; cand.sa_val = sa_val; cand.name = ckt.gates[in_wire].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
                cand.is_gi = true; cand.target_gate_id = gid; cand.target_fanin_idx = fi_idx; cand.loc_str = g.name + " GI";
                raw_candidates.push_back(cand);
            }
        }
    }
    vector<FaultGroup> groups;
    unordered_map<uint64_t, int> sig2group;
    vector<FaultGroup> dummy_groups; 
    for(auto& c : raw_candidates) dummy_groups.push_back({c, {}});
    for (size_t i = 0; i < raw_candidates.size(); ++i) {
        auto& cand = raw_candidates[i];
        sim.simulate_multi(ckt, {(int)i}, dummy_groups, obs_fail_matrix, cand.tfsf, cand.tpsf, cand.tfsp, cand.init_iou, &cand.sig_hash);
        if (cand.tfsf == 0) continue; 
        auto it = sig2group.find(cand.sig_hash);
        if (it != sig2group.end()) {
            groups[it->second].equivs.push_back(cand);
        } else {
            sig2group[cand.sig_hash] = groups.size();
            groups.push_back({cand, {}});
        }
    }
    sort(groups.begin(), groups.end(), [](const FaultGroup& a, const FaultGroup& b) {
        return a.rep.init_iou > b.rep.init_iou;
    });
    
    // 【高 Accuracy 配置】擴大搜尋空間，確保真正的 Multi-fault 不被誤殺
    int POOL_SIZE = min(150, (int)groups.size()); 
    int BEAM_WIDTH = 60;
    int MAX_DEPTH = 7; 
    
    vector<BeamState> beam;
    BeamState best_overall; best_overall.iou = -1.0;
    for (int i = 0; i < POOL_SIZE; ++i) {
        BeamState s; s.combo.push_back(i);
        s.tfsf = groups[i].rep.tfsf; s.tpsf = groups[i].rep.tpsf; s.tfsp = groups[i].rep.tfsp;
        s.iou = groups[i].rep.init_iou;
        beam.push_back(s);
        if (s.iou > best_overall.iou) best_overall = s;
    }
    
    for (int depth = 2; depth <= MAX_DEPTH; ++depth) {
        vector<BeamState> next_beam;
        for (const auto& state : beam) {
            if (state.tpsf == 0 && state.tfsp == 0) { 
                next_beam.push_back(state); continue;
            }
            for (int i = 0; i < POOL_SIZE; ++i) {
                if (i <= state.combo.back()) continue; 
                bool conflict = false;
                for (int idx : state.combo) {
                    if (groups[idx].rep.wire_id == groups[i].rep.wire_id) { conflict = true; break; }
                }
                if (conflict) continue;
                BeamState ns = state;
                ns.combo.push_back(i);
                sim.simulate_multi(ckt, ns.combo, groups, obs_fail_matrix, ns.tfsf, ns.tpsf, ns.tfsp, ns.iou);
                
                // 【減輕懲罰】讓深層的正確組合能浮出水面
                ns.iou -= (depth * 0.00005); 
                next_beam.push_back(ns);
                
                bool is_better = false;
                if (ns.iou > best_overall.iou + 1e-5) {
                    is_better = true;
                } else if (abs(ns.iou - best_overall.iou) <= 1e-5 && ns.combo.size() < best_overall.combo.size()) {
                    is_better = true; 
                }
                if (is_better) best_overall = ns;
            }
        }
        sort(next_beam.begin(), next_beam.end(), [](const BeamState& a, const BeamState& b) {
            if (abs(a.iou - b.iou) > 1e-5) return a.iou > b.iou;
            return a.combo.size() < b.combo.size(); 
        });
        if ((int)next_beam.size() > BEAM_WIDTH) next_beam.resize(BEAM_WIDTH);
        beam = next_beam;
        if (best_overall.tpsf == 0 && best_overall.tfsp == 0) break; 
    }

    // =========================================================
    // 5. Post-Search Redundancy Elimination (保住 Resolution)
    // =========================================================
    vector<int> minimal_combo;
    for (size_t i = 0; i < best_overall.combo.size(); ++i) {
        vector<int> test_combo;
        for (size_t j = 0; j < best_overall.combo.size(); ++j) {
            if (i != j) test_combo.push_back(best_overall.combo[j]);
        }
        int t_tfsf = 0, t_tpsf = 0, t_tfsp = 0; double t_iou = 0.0;
        if (!test_combo.empty()) sim.simulate_multi(ckt, test_combo, groups, obs_fail_matrix, t_tfsf, t_tpsf, t_tfsp, t_iou);
        
        bool is_redundant = false;
        if (abs(t_iou - best_overall.iou) < 1e-5) is_redundant = true;
        if (t_tpsf == 0 && t_tfsp == 0 && best_overall.tpsf == 0 && best_overall.tfsp == 0) is_redundant = true;
        
        if (!is_redundant) minimal_combo.push_back(best_overall.combo[i]);
    }
    best_overall.combo = minimal_combo;
    if (!best_overall.combo.empty()) {
        sim.simulate_multi(ckt, best_overall.combo, groups, obs_fail_matrix, best_overall.tfsf, best_overall.tpsf, best_overall.tfsp, best_overall.iou);
    }

    cout << "#Circuit Summary:\n#---------------\n";
    cout << "#number of inputs = " << ckt.pis.size() << "\n#number of outputs = " << ckt.pos.size() << "\n";
    cout << "#number of gates = " << (ckt.num_wires - ckt.pis.size() - ckt.pos.size()) << "\n#number of wires = " << ckt.num_wires << "\n";
    cout << "#number of vectors = " << patterns.size() << "\n#number of failing outputs = " << fails.size() << "\n";
    cout << "Ranked suspect faults\n";
    int rank = 1;
    unordered_set<int> printed_group_idx;
    auto print_group = [&](int idx, double assign_score, int d_tfsf, int d_tpsf, int d_tfsp) {
        const auto& rep = groups[idx].rep;
        const auto& equivs = groups[idx].equivs;
        set<string> printed_names; 
        printed_names.insert(rep.name);
        vector<string> eq_strs;
        for (const auto& eq : equivs) {
            if (printed_names.find(eq.name) == printed_names.end()) {
                printed_names.insert(eq.name);
                eq_strs.push_back(eq.name + " " + eq.loc_str + " " + eq.type_str);
            }
        }
        cout << "No. " << rank << " " << rep.name << " " << rep.loc_str << " " << rep.type_str
             << ", TFSF=" << d_tfsf << ", TPSF=" << d_tpsf << ", TFSP=" << d_tfsp
             << ", score=" << fixed << setprecision(1) << assign_score;
        if (!eq_strs.empty()) {
            cout << " [equivalent faults: ";
            for (size_t k = 0; k < eq_strs.size(); ++k) cout << eq_strs[k] << (k == eq_strs.size() - 1 ? "" : ", ");
            cout << "]";
        }
        cout << "\n"; rank++;
        printed_group_idx.insert(idx);
    };
    
    for (int idx : best_overall.combo) {
        if (rank > 10) break;
        double pure_iou = (double)best_overall.tfsf / (best_overall.tfsf + best_overall.tpsf + best_overall.tfsp + 1e-9);
        print_group(idx, pure_iou * 100.0, groups[idx].rep.tfsf, groups[idx].rep.tpsf, groups[idx].rep.tfsp);
    }
    for (size_t i = 0; i < groups.size() && rank <= 10; ++i) {
        if (printed_group_idx.count(i)) continue;
        double pure_iou = (double)groups[i].rep.tfsf / (groups[i].rep.tfsf + groups[i].rep.tpsf + groups[i].rep.tfsp + 1e-9);
        print_group(i, pure_iou * 100.0, groups[i].rep.tfsf, groups[i].rep.tpsf, groups[i].rep.tfsp);
    }
    auto end_time = high_resolution_clock::now(); duration<double> diff = end_time - start_time;
    cout << "# run time = " << fixed << setprecision(3) << diff.count() << "s\n";
}

int main(int argc, char** argv) {
    ios_base::sync_with_stdio(false); cin.tie(NULL);
    try {
        if (argc < 2) return 1;
        string mode = argv[1];
        if (mode == "-diag") { if (argc < 5) return 1; run_diag(argv[2], argv[3], argv[4]); return 0; }
        return 1;
    } catch (...) { return 1; }
}
