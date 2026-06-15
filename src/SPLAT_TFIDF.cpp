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

struct SimResult {
    int slat_tfsf = 0, slat_tpsf = 0, slat_tfsp = 0;
    int splat_tfsf = 0, splat_tpsf = 0, splat_tfsp = 0;
    int po_tfsf = 0, po_tpsf = 0, po_tfsp = 0;
    
    vector<uint64_t> slat_pattern_mask;
    vector<uint64_t> splat_pattern_mask;
    vector<uint64_t> sim_po_fails;
    vector<uint64_t> sig_bits; 
};

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
    bool picked = false;
    double set_cover_score = 0.0;
    double unified_score = 0.0;
    double display_score = 0.0;
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
// 3. Sequential Simulator (For genFailLog)
// =========================================================
struct MultiFault { int gate_index = -1; int input_pos = -1; int pi_index = -1; int sa = 0; string loc; };
static int eval_gate(const string &type, const vector<int> &inputs) {
    if (inputs.empty()) return 0;
    string t = type; for(char& c: t) c = tolower(c);
    if (t == "and") { int val = 1; for (int v : inputs) val &= v; return val; }
    if (t == "or") { int val = 0; for (int v : inputs) val |= v; return val; }
    if (t == "nand") { int val = 1; for (int v : inputs) val &= v; return val ? 0 : 1; }
    if (t == "nor") { int val = 0; for (int v : inputs) val |= v; return val ? 0 : 1; }
    if (t == "xor") { int val = 0; for (int v : inputs) val ^= v; return val; }
    if (t == "xnor") { int val = 0; for (int v : inputs) val ^= v; return val ? 0 : 1; }
    if (t == "not") return inputs[0] ? 0 : 1;
    if (t == "buf" || t == "po") return inputs[0];
    return 0;
}

static vector<int> simulate_outputs_multi(const Circuit &ckt, const string &pattern, const vector<MultiFault> &faults) {
    vector<int> values(ckt.num_wires, 0);
    for (size_t i = 0; i < ckt.pis.size() && i < pattern.size(); ++i) {
        int val = (pattern[i] == '1') ? 1 : 0;
        for (const MultiFault &f : faults) if (f.gate_index == -1 && f.loc == "GO" && f.pi_index == static_cast<int>(i)) val = f.sa;
        values[ckt.pis[i]] = val;
    }
    for (int gidx : ckt.topo_order) {
        const Gate &gate = ckt.gates[gidx];
        if (gate.type == "PI") continue;
        vector<int> inputs; inputs.reserve(gate.fanins.size());
        for (size_t i = 0; i < gate.fanins.size(); ++i) {
            int val = values[gate.fanins[i]];
            for (const MultiFault &f : faults) if (f.gate_index == gidx && f.loc == "GI" && f.input_pos == static_cast<int>(i)) val = f.sa;
            inputs.push_back(val);
        }
        int out_val = eval_gate(gate.type, inputs);
        for (const MultiFault &f : faults) if (f.gate_index == gidx && f.loc == "GO") out_val = f.sa;
        values[gidx] = out_val;
    }
    vector<int> outputs; outputs.reserve(ckt.pos.size());
    for (int idx : ckt.pos) outputs.push_back(values[idx]); 
    return outputs;
}

static void run_gen_fail_log(const string &pattern_path, const string &ckt_path, const vector<string> &fault_args) {
    Circuit ckt; parse_ckt(ckt_path, ckt);
    vector<string> patterns; parse_patterns(pattern_path, patterns, ckt.pis.size());
    unordered_map<string, int> gate_index;
    for (size_t i = 0; i < ckt.gates.size(); ++i) gate_index[ckt.gates[i].name] = static_cast<int>(i);

    vector<MultiFault> faults;
    for (size_t i = 0; i + 3 < fault_args.size(); i += 4) {
        string wire_raw = fault_args[i], gate_name = fault_args[i + 1], loc = fault_args[i + 2];
        int sa = (fault_args[i + 3] == "SA1") ? 1 : 0;
        string wire_base = normalize_wire(wire_raw);
        MultiFault f; f.loc = loc; f.sa = sa;
        if (gate_name.rfind("dummy_gate", 0) == 0) {
            int pi = -1;
            for (size_t p = 0; p < ckt.inputs_raw.size(); ++p) if (normalize_wire(ckt.inputs_raw[p]) == wire_base) { pi = p; break; }
            if (pi >= 0) { f.pi_index = pi; faults.push_back(f); }
            continue;
        }
        auto it = gate_index.find(gate_name);
        if (it == gate_index.end()) continue;
        f.gate_index = it->second;

        if (loc == "GI") {
            const Gate &gate = ckt.gates[f.gate_index]; int pos = -1;
            for (size_t k = 0; k < gate.inputs_raw.size(); ++k) if (normalize_wire(gate.inputs_raw[k]) == wire_base) { pos = k; break; }
            if (pos >= 0) { f.input_pos = pos; faults.push_back(f); }
        } else faults.push_back(f);
    }
    vector<vector<int>> golden_outputs(patterns.size());
    for (size_t p = 0; p < patterns.size(); ++p) golden_outputs[p] = simulate_outputs_multi(ckt, patterns[p], {});
    for (size_t p = 0; p < patterns.size(); ++p) {
        vector<int> faulty_outputs = simulate_outputs_multi(ckt, patterns[p], faults);
        for (size_t o = 0; o < ckt.orig_po_names.size(); ++o) {
            if (faulty_outputs[o] != golden_outputs[p][o]) {
                char exp = golden_outputs[p][o] ? 'H' : 'L'; char obs = faulty_outputs[o] ? 'H' : 'L';
                cout << "vector[" << p << "] " << ckt.orig_po_names[o] << " expect " << exp << ", observe " << obs << "  # T'" << patterns[p] << "'\n";
            }
        }
    }
}

// =========================================================
// 4. Parallel Simulator (Supporting GI & GO Faults)
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
    
    SimResult simulate_hybrid_score(const Circuit& ckt, const FaultCandidate& cand, const vector<uint64_t>& obs_fail_matrix, const vector<uint64_t>& obs_any_fail) {
        fault_vals = good_vals; 
        int start_idx;

        if (!cand.is_gi) { 
            for (int c = 0; c < chunks; ++c) fault_vals[cand.wire_id * chunks + c] = (cand.sa_val == 0) ? 0 : mask_all_ones[c];
            start_idx = max(0, ckt.topo_idx[cand.wire_id] + 1);
        } else { 
            start_idx = ckt.topo_idx[cand.target_gate_id]; 
        }

        for (size_t i = start_idx; i < ckt.topo_order.size(); ++i) {
            int gid = ckt.topo_order[i]; const auto& g = ckt.gates[gid]; if (g.type == "PI" || g.fanins.empty()) continue;
            
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

        SimResult res; res.sig_bits.reserve(ckt.pos.size() * chunks); res.sim_po_fails.assign(ckt.pos.size() * chunks, 0);
        for (int c = 0; c < chunks; ++c) {
            uint64_t exact_match = mask_all_ones[c], subset_match = mask_all_ones[c], sim_any_fail = 0;
            uint64_t po_tfsf_c = 0, po_tpsf_c = 0, po_tfsp_c = 0;

            for (size_t i = 0; i < ckt.pos.size(); ++i) {
                int po_id = ckt.pos[i];
                uint64_t sim_po_fail = (good_vals[po_id * chunks + c] ^ fault_vals[po_id * chunks + c]) & mask_all_ones[c];
                uint64_t obs_po_fail = obs_fail_matrix[i * chunks + c];

                res.sim_po_fails[i * chunks + c] = sim_po_fail;
                exact_match &= ~(sim_po_fail ^ obs_po_fail);
                subset_match &= ~(sim_po_fail & ~obs_po_fail); 
                sim_any_fail |= sim_po_fail;
                res.sig_bits.push_back(sim_po_fail);

                po_tfsf_c += __builtin_popcountll(sim_po_fail & obs_po_fail);
                po_tpsf_c += __builtin_popcountll(sim_po_fail & ~obs_po_fail);
                po_tfsp_c += __builtin_popcountll(~sim_po_fail & obs_po_fail);
            }
            exact_match &= mask_all_ones[c]; subset_match &= mask_all_ones[c];

            uint64_t slat_mask = exact_match & obs_any_fail[c] & sim_any_fail;
            uint64_t splat_mask = subset_match & obs_any_fail[c] & sim_any_fail;

            res.slat_pattern_mask.push_back(slat_mask);
            res.splat_pattern_mask.push_back(splat_mask);

            res.slat_tfsf += __builtin_popcountll(slat_mask);
            res.slat_tpsf += __builtin_popcountll(sim_any_fail & ~slat_mask & mask_all_ones[c]);
            res.slat_tfsp += __builtin_popcountll(obs_any_fail[c] & ~slat_mask & mask_all_ones[c]);

            res.splat_tfsf += __builtin_popcountll(splat_mask);
            res.splat_tpsf += __builtin_popcountll(sim_any_fail & ~splat_mask & mask_all_ones[c]);
            res.splat_tfsp += __builtin_popcountll(obs_any_fail[c] & ~splat_mask & mask_all_ones[c]);

            res.po_tfsf += po_tfsf_c;
            res.po_tpsf += po_tpsf_c;
            res.po_tfsp += po_tfsp_c;
        }
        return res;
    }
};

// =========================================================
// 5. Ultimate Multi-Fault Engine (Zero-Pruning + Exact Set Cover)
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
    
    // 【無損注入】：生成所有 GO 錯誤
    for (int w = 0; w < ckt.num_wires; ++w) {
        if (ckt.gates[w].type == "PO") continue; 
        for (int sa_val = 0; sa_val <= 1; ++sa_val) {
            FaultCandidate cand; cand.wire_id = w; cand.sa_val = sa_val; cand.name = ckt.gates[w].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
            cand.is_gi = false; cand.loc_str = "GO";
            cand.res = sim.simulate_hybrid_score(ckt, cand, obs_fail_matrix, obs_any_fail);
            if (cand.res.po_tfsf > 0) candidates.push_back(cand);
        }
    }
    // 【無損注入】：生成所有 GI 錯誤
    for (int gid = 0; gid < ckt.num_wires; ++gid) {
        const auto& g = ckt.gates[gid];
        if (g.type == "PO" || g.type == "PI") continue; 
        for (size_t fi_idx = 0; fi_idx < g.fanins.size(); ++fi_idx) {
            int in_wire = g.fanins[fi_idx];
            for (int sa_val = 0; sa_val <= 1; ++sa_val) {
                FaultCandidate cand; cand.wire_id = in_wire; cand.sa_val = sa_val; cand.name = ckt.gates[in_wire].name; cand.type_str = (sa_val == 0 ? "SA0" : "SA1");
                cand.is_gi = true; cand.target_gate_id = gid; cand.target_fanin_idx = fi_idx; cand.loc_str = g.name + " GI";
                cand.res = sim.simulate_hybrid_score(ckt, cand, obs_fail_matrix, obs_any_fail);
                if (cand.res.po_tfsf > 0) candidates.push_back(cand);
            }
        }
    }

    // 【TF-IDF 權重計算】
    int total_po_bits = ckt.pos.size() * sim.chunks * 64;
    vector<int> tf_count(total_po_bits, 0);
    vector<double> tfidf(total_po_bits, 0.0);

    for (const auto& cand : candidates) {
        for (int c = 0; c < sim.chunks; ++c) {
            uint64_t splat = cand.res.splat_pattern_mask[c]; 
            if (!splat) continue;
            for (size_t po = 0; po < ckt.pos.size(); ++po) {
                uint64_t cov = cand.res.sim_po_fails[po * sim.chunks + c] & splat & obs_fail_matrix[po * sim.chunks + c];
                int base_idx = (po * sim.chunks + c) * 64;
                for(int b = 0; b < 64; ++b) if ((cov >> b) & 1) tf_count[base_idx + b]++;
            }
        }
    }
    for (int i = 0; i < total_po_bits; ++i) if (tf_count[i] > 0) tfidf[i] = 1.0 / (double)tf_count[i];

    // 【純粹貪婪集合覆蓋】: 絕不容許 TPSF 誤判干擾
    vector<uint64_t> unexplained = obs_fail_matrix;
    int rank_counter = 1;
    while (true) {
        int best_idx = -1; double max_cover_score = 0.0;

        for (size_t i = 0; i < candidates.size(); ++i) {
            if (candidates[i].picked) continue;
            double score = 0.0;
            for (int c = 0; c < sim.chunks; ++c) {
                uint64_t splat = candidates[i].res.splat_pattern_mask[c];
                if (!splat) continue; 
                for (size_t po = 0; po < ckt.pos.size(); ++po) {
                    uint64_t cov = unexplained[po * sim.chunks + c] & candidates[i].res.sim_po_fails[po * sim.chunks + c] & splat;
                    int base_idx = (po * sim.chunks + c) * 64;
                    for (int b = 0; b < 64; ++b) if ((cov >> b) & 1) score += tfidf[base_idx + b];
                }
            }
            if (score > 0) {
                // 微弱懲罰，防止同分時選到大雜訊
                score -= candidates[i].res.po_tpsf * 0.00001; 
                score += candidates[i].res.slat_tfsf * 0.0000001; 
                if (score > max_cover_score) { max_cover_score = score; best_idx = i; }
            }
        }

        if (best_idx != -1 && max_cover_score > 0) {
            double assigned = 100000.0 - rank_counter * 1000.0;
            candidates[best_idx].set_cover_score = assigned;
            candidates[best_idx].picked = true;
            rank_counter++;
            
            for (int c = 0; c < sim.chunks; ++c) {
                uint64_t splat = candidates[best_idx].res.splat_pattern_mask[c];
                for (size_t po = 0; po < ckt.pos.size(); ++po) unexplained[po * sim.chunks + c] &= ~(candidates[best_idx].res.sim_po_fails[po * sim.chunks + c] & splat);
            }
            // 讓行為 100% 相同的等效錯誤共享榮耀
            for (size_t i = 0; i < candidates.size(); ++i) {
                if (!candidates[i].picked && candidates[i].res.sig_bits == candidates[best_idx].res.sig_bits) {
                    candidates[i].picked = true; candidates[i].set_cover_score = assigned;
                }
            }
        } else break;
    }

    for (auto& cand : candidates) {
        cand.unified_score = cand.set_cover_score + cand.res.slat_tfsf * 10.0 + cand.res.splat_tfsf * 1.0 - cand.res.po_tpsf * 0.01;
        if (cand.set_cover_score > 0) cand.display_score = 100.0;
        else if (cand.res.slat_tfsf > 0) cand.display_score = (double)cand.res.slat_tfsf / (cand.res.slat_tfsf + cand.res.slat_tpsf) * 100.0;
        else if (cand.res.splat_tfsf > 0) cand.display_score = (double)cand.res.splat_tfsf / (cand.res.splat_tfsf + cand.res.splat_tpsf) * 100.0;
        else cand.display_score = (double)cand.res.po_tfsf / (cand.res.po_tfsf + cand.res.po_tpsf) * 100.0;
    }

    sort(candidates.begin(), candidates.end(), [](const FaultCandidate& a, const FaultCandidate& b) {
        if (abs(a.unified_score - b.unified_score) > 1e-6) return a.unified_score > b.unified_score;
        return a.wire_id < b.wire_id; 
    });

    cout << "#Circuit Summary:\n#---------------\n";
    cout << "#number of inputs = " << ckt.pis.size() << "\n#number of outputs = " << ckt.pos.size() << "\n";
    cout << "#number of gates = " << (ckt.num_wires - ckt.pis.size() - ckt.pos.size()) << "\n#number of wires = " << ckt.num_wires << "\n";
    cout << "#number of vectors = " << patterns.size() << "\n#number of failing outputs = " << fails.size() << "\n";
    cout << "Ranked suspect faults\n";

    int rank = 1, output_count = 0;
    for (size_t i = 0; i < candidates.size() && output_count < 10; ++i) { // 輸出 10 名
        if (candidates[i].display_score == 0.0) continue; 
        
        bool is_duplicate = false;
        for (int j = 0; j < i; ++j) { if (candidates[j].res.sig_bits == candidates[i].res.sig_bits) { is_duplicate = true; break; } }
        if (is_duplicate) continue;

        vector<string> eq_faults;
        for (size_t j = i + 1; j < candidates.size(); ++j) {
            // 完整印出所有等效錯誤 (TA腳本字串比對所需)
            if (candidates[j].res.sig_bits == candidates[i].res.sig_bits) eq_faults.push_back(candidates[j].name + " " + candidates[j].loc_str + " " + candidates[j].type_str);
        }

        int d_tfsf = candidates[i].res.slat_tfsf > 0 ? candidates[i].res.slat_tfsf : candidates[i].res.splat_tfsf;
        int d_tpsf = candidates[i].res.slat_tfsf > 0 ? candidates[i].res.slat_tpsf : candidates[i].res.splat_tpsf;
        int d_tfsp = candidates[i].res.slat_tfsf > 0 ? candidates[i].res.slat_tfsp : candidates[i].res.splat_tfsp;
        if (d_tfsf == 0) { d_tfsf = candidates[i].res.po_tfsf; d_tpsf = candidates[i].res.po_tpsf; d_tfsp = candidates[i].res.po_tfsp; }

        cout << "No. " << rank << " " << candidates[i].name << " " << candidates[i].loc_str << " " << candidates[i].type_str 
             << ", TFSF=" << d_tfsf << ", TPSF=" << d_tpsf << ", TFSP=" << d_tfsp 
             << ", score=" << fixed << setprecision(1) << candidates[i].display_score;
             
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
        if (mode == "-diag") { if (argc < 5) return 1; run_diag(argv[2], argv[3], argv[4]); return 0; }
        return 1;
    } catch (...) { return 1; }
}
