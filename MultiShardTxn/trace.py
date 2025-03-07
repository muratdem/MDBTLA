import json
import os
import random
import argparse
import time

import cover

# 
# Experiments in model-based test case generation for the WiredTiger API based on TLA+ model.
# 

WT_TEST_TEMPLATE = open("test_txn_model_template.py").read()
WT_TEST_FN_TEMPLATE = """
    def test_trace_1(self):
        key_format,value_format = "S","S"
        self.uri = 'table:test_txn01'
        self.session.create(self.uri, 'key_format=' + key_format + ',value_format=' + value_format)
        conn = self.conn
        self.cursors = {}
"""

def make_wt_action(pre_state, action_name, action_args, post_state):
    # print(action_name)
    tid = ""
    err_code = None
    if "tid" in action_args:
        tid = action_args['tid']
        err_code = 0
        # print(post_state)
        if post_state is not None:
            err_code = post_state[1]['txnStatus']["n"][tid]
    wt_action_name = action_name.lower().replace("mdbtxn", "transaction_")
    # txn_cursor = f"self.cursor_{tid}"
    txn_cursor = f"self.cursors[\"{tid}\"]"
    # print(err_code)
    txn_session = f"sess_{tid}"
    ignore_prepare = "false"
    if "ignorePrepare" in action_args:
        ignore_prepare = action_args['ignorePrepare'].replace("\"", "")
    if action_name == "StartTransaction":
        # wt_action_name = f"{txn_session}.begin_transaction('ignore_prepare={ignore_prepare},read_timestamp=' + self.timestamp_str({action_args['readTs']}));{txn_cursor} = {txn_session}.open_cursor(self.uri, None)"
        wt_action_name = f"self.begin_transaction(txn_session, {ignore_prepare},{action_args['readTs']}));{txn_cursor} = {txn_session}.open_cursor(self.uri, None)"
    if action_name == "TransactionWrite":
        wt_action_name = f"{txn_cursor}.set_key(\"{action_args['k']}\");{txn_cursor}.set_value(\"{action_args['v']}\");{txn_cursor}.insert()"
    if action_name == "TransactionRead":
        wt_action_name = f"{txn_cursor}.set_key(\"{action_args['k']}\");sret = {txn_cursor}.search()"
        if action_args['v'] == "NoValue":
            wt_action_name += f";self.assertEquals(sret, wiredtiger.WT_NOTFOUND)"
        else:
            wt_action_name += f";self.assertEquals({txn_cursor}.get_value(), \"{action_args['v']}\")"
    if action_name == "TransactionRemove":
        wt_action_name = f"{txn_cursor}.set_key(\"{action_args['k']}\");sret = {txn_cursor}.remove()"
    if action_name == "PrepareTransaction":
        wt_action_name = f"{txn_session}.prepare_transaction('prepare_timestamp=' + self.timestamp_str({action_args['prepareTs']}))"
    if action_name == "CommitTransaction":
        args = f"'commit_timestamp=' + self.timestamp_str({action_args['commitTs']})"
        wt_action_name = f"{txn_session}.commit_transaction({args})"
    if action_name == "CommitPreparedTransaction":
        # Specify commit and durable timestamps (prepared transactions require both.).
        args = f"'commit_timestamp=' + self.timestamp_str({action_args['commitTs']}) + ',durable_timestamp=' + self.timestamp_str({action_args['durableTs']})"
        wt_action_name = f"{txn_session}.commit_transaction({args})"
    if action_name == "AbortTransaction":
        wt_action_name = f"{txn_session}.rollback_transaction()"
    if action_name == "SetStableTimestamp":
        wt_action_name = f"self.conn.set_timestamp('stable_timestamp='+self.timestamp_str({action_args['ts']}))"
    if action_name == "SetOldestTimestamp":
        wt_action_name = f"self.conn.set_timestamp('oldest_timestamp='+self.timestamp_str({action_args['ts']}))"
    if action_name == "RollbackToStable":
        wt_action_name = f"self.conn.rollback_to_stable()"
    # wt_args = [str(action_args[p]) for p in action_args]
    # return f"{wt_action_name}, {err_code}"
    lines = [
        "res,sret = None,None",
        "try:",
        f"    {wt_action_name}",
        "except wiredtiger.WiredTigerError as e:",
        "    res = e"
    ]
    res_expected = None
    exception_str = None
    if err_code == "WT_ROLLBACK":
        lines.append("self.assertNotEqual(res, None)")
        res_expected = 1
        exception_str = "wiredtiger.WT_ROLLBACK"
        lines.append("self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_ROLLBACK) in str(res))")
    elif err_code == "WT_NOTFOUND":
        # lines.append("self.assertEqual(res, None)")
        lines.append("self.assertEqual(sret, wiredtiger.WT_NOTFOUND)")
    elif err_code == "WT_PREPARE_CONFLICT":
        lines.append("self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_PREPARE_CONFLICT) in str(res))")
    else:
        lines.append("self.assertEquals(res, None)")
        if action_name == "TransactionRemove":
            lines.append("self.assertEquals(sret, 0)")

    #
    # More compact action output.
    #
    if action_name == "StartTransaction":
        lines = [ f"self.begin_transaction(\"{tid}\", {txn_session}, {action_args['readTs']}, \"{ignore_prepare}\", {res_expected}, \"{err_code}\")" ]
    if action_name == "TransactionWrite":
        lines = [ f"self.transaction_write(\"{tid}\", \"{action_args['k']}\", {res_expected}, \"{err_code}\")"]
    if action_name == "TransactionRead":
        lines = [ f"self.transaction_read(\"{tid}\", \"{action_args['k']}\", \"{action_args['v']}\", {res_expected}, \"{err_code}\")" ]
    if action_name == "TransactionRemove":
        lines = [ f"self.transaction_remove(\"{tid}\", \"{action_args['k']}\", {res_expected}, \"{err_code}\")" ]
    if action_name == "CommitTransaction":
        lines = [ f"self.commit_transaction({txn_session}, \"{tid}\", {action_args['commitTs']}, {res_expected}, \"{err_code}\")" ]
    if action_name == "CommitPreparedTransaction":
        lines = [ f"self.commit_prepared_transaction({txn_session}, {action_args['commitTs']}, {action_args['durableTs']}, {res_expected}, \"{err_code}\")" ]
    if action_name == "PrepareTransaction":
        lines = [ f"self.prepare_transaction({txn_session}, {action_args['prepareTs']}, {res_expected}, \"{err_code}\")" ]

    # TODO: Enable this again once implemented in model.
    # all_durable_ts = post_state[1]['allDurableTs']["n"]
    # lines += [f"self.check_timestamps(all_durable='{all_durable_ts}')"]
    
    return lines

def gen_wt_test_from_traces(traces, max_len=1000, compact=False, cvg_pct=1.0):
    # print("\n-----\nWT Actions:")

    # Open a separate session for all transactions.
    txns = ["t1", "t2", "t3"]

    f = open("test_txn_model_traces.py", "w")
    f.write(f"#\n")
    f.write(f"# coverage_pct = {cvg_pct}\n")
    f.write(f"# {len(traces)} traces\n")
    f.write(f"#\n")
    f.write(f"\n")
    f.write(WT_TEST_TEMPLATE)

    tab = lambda  n : "    " * n

    for i, trace in enumerate(traces):

        wt_actions = []
            
        # Print each action in the trace
        for action in trace['action'][:max_len]:
            # Each action has 3 elements: initial state, transition info, final state
            pre_state = action[0]
            transition = action[1] 
            action_args = []
            if "context" in transition:
                action_args = transition['context']
            post_state = action[2]
            
            # print("\nAction:", transition['name'])
            # print("Initial State:", init_state)
            # print("Parameters:", action_args)
            # print("Parameters:", transition['parameters'])
            # print("Context:", transition['context'])
            # print("Final State:", final_state)
            wt_actions.append(make_wt_action(pre_state, transition['name'], action_args, post_state))


        f.write(WT_TEST_FN_TEMPLATE.replace("test_trace_1", f"test_trace_{i}"))

        f.write(tab(2))
        txns_sessions = [f"sess_{t} = conn.open_session()" for t in txns]
        f.write(";".join(txns_sessions))
        # print("")
        f.write("\n")
        action_labels = []
        action_labels_only = []
        test_lines = []
        for i, a in enumerate(wt_actions):
            action_name = trace['action'][i][1]['name']
            action_ctx = {}
            params = []
            if "context" in trace['action'][i][1]:
                action_ctx = trace['action'][i][1]['context']
            if "parameters" in trace['action'][i][1]:
                params = trace['action'][i][1]['parameters']

            post_state = trace['action'][i][2][1]
            # print(action_ctx)
            action_params_str = ', '.join([str(p) + "=" + str(action_ctx[p]) for p in action_ctx])
            # print(post_state)
            txn_post_state = None
            tid = None
            if "tid" in action_ctx:
                tid = action_ctx['tid']
                txn_post_state = post_state['txnStatus']["n"][tid]
            action_label = f"# [Action {i+1}]: {action_name}({action_params_str}) res:{txn_post_state}"
            post_state_label = "\n" + str("\n".join([tab(3) +  "# " + str(k) + " = " + str(post_state[k]) for k in post_state.keys()]))
            if not compact:
                action_labels_only.append(tab(2) + action_label)
                action_labels.append(tab(2) + action_label + "\n" + tab(2) + post_state_label + "\n")
            # print(action_label)
            # print(a)
            # print("")
            # test_lines.append(tab(2) + action_label)
            # test_lines.append("\n")
            for l in a:
                test_lines.append(tab(2) + l + "\n")
            # test_lines.append("\n")
        f.write("\n")
        if not compact:
            f.write("\n".join(action_labels_only))
            f.write("\n\n")
            f.write("\n".join(action_labels))
            f.write("\n\n\n")
        f.writelines(test_lines)
        f.write(tab(2) + "self.debug_info()\n")
    f.close()

def gen_tla_model_trace(json_trace="trace.json", seed=0):
    tlc = "java -cp /usr/local/bin/tla2tools-v1.8.jar tlc2.TLC -noGenerateSpecTE"
    specname = "Storage"
    cmd = f"{tlc} -seed {seed} -dumpTrace json {json_trace} -simulate -workers 1 -cleanup -deadlock {specname}.tla"
    # print(cmd)
    os.system(cmd)

def gen_tla_json_graph(json_graph="states.json", seed=0, specname="Storage", constants={}, symmetry=False):

    # Optionally disabled actions.
    disabled_actions = [
        "SetStableTimestamp",
        "RollbackToStable"
    ]

    # For now don't use symmetry when doing trace generation.
    config = {
        "init": "Init",
        "next": "Next",
        "symmetry": "Symmetry" if symmetry else None,
        # "constraint": "StateConstraint",
        "constants": {
            "RC": "\"snapshot\"",
            "WC": "\"majority\"",
            "Nil": "Nil",
            "Keys": "{k1,k2}",
            "MTxId": "{t1,t2}",
            "Node": "{n}",
            "NoValue": "NoValue",
            "MaxOpsPerTxn": "2",
            "Timestamps": "{1,2,3}"
        },
        "overrides": {}
    }

    for a in disabled_actions:
        config["overrides"][a] = "FALSE"

    # Optionally passed in constant overrides.
    for c in constants:
        config["constants"][c] = constants[c]

    # Create TLC config file from JSON config.
    model_fname = f"{specname}_gen.cfg"
    with open(model_fname, "w") as f:
        f.write("INIT " + config["init"] + "\n")
        f.write("NEXT " + config["next"] + "\n")
        for k, v in config["constants"].items():
            f.write(f"CONSTANT {k} = {v}\n")
        if "constraint" in config:
            f.write("CONSTRAINT " + config["constraint"] + "\n")
        # f.write("INVARIANT " + config["invariant"] + "\n")
        if "overrides" in config:
            for k, v in config["overrides"].items():
                f.write(f"{k} <- {v}\n")
        if "symmetry" in config and config["symmetry"] is not None:
            f.write("SYMMETRY " + config["symmetry"] + "\n")

        # json.dump(config, f)
        f.close()

    tlc = "java -Xmx20g -cp tla2tools-json.jar tlc2.TLC -noGenerateSpecTE"
    fp = 10 # use a constant FP.
    cmd = f"{tlc} -seed {seed} -dump json {json_graph} -fp {fp} -workers 10 -deadlock -config {model_fname} {specname}.tla"
    print(cmd)
    os.system(cmd)


if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument('--ntests', type=int, default=50, help='Number of test traces to generate')
    parser.add_argument('--coverage_pct', type=float, default=1.0, help='Percentage of states to cover')
    parser.add_argument('--compact', action='store_true', help='Generate compact test cases', default=False)
    parser.add_argument('--constants', type=str, default="", help='Constant overrides', nargs='+')
    parser.add_argument('--generate_only', action='store_true', help='Generate state graphs only and return.', default=False)
    parser.add_argument('--use_cached_graphs', action='store_true', help='Load cached JSON state graph')
    
    args = parser.parse_args()
    ntests = args.ntests

    constants = {}
    for i in range(0, len(args.constants), 2):
        k = args.constants[i]
        v = args.constants[i+1]
        constants[k] = v
    if len(constants.keys()) > 0:
        print("Using passed in constants:", constants)

    #
    # Re-generate state graph.
    # 
    # java -cp tla2tools-json.jar tlc2.TLC -dump json states.json -workers 10 -deadlock MDBTest
    # 
    now = time.time()
    if not args.use_cached_graphs:
        gen_tla_json_graph("states.json", specname="Storage", constants=constants)
        print("--> Generated JSON state graph.")

        # Generate state graph under symmetry reduction.
        gen_tla_json_graph("states_symmetric.json", specname="Storage", constants=constants, symmetry=True)
        print("--> Generated JSON state graph under symmetry reduction.")
    else:
        print("--> Using cached JSON state graphs.")

    if args.generate_only:
        print("--> Exiting after generating JSON state graphs.")
        exit(0)

    # Parse graphs.
    G, node_map, edge_actions = cover.parse_json_state_graph("states.json")
    G_symm, node_map_symm, edge_actions_symm = cover.parse_json_state_graph("states_symmetric.json")

    print("Num states in non-symmetric graph:", len(node_map.keys()))
    print("Num states in symmetric graph:", len(node_map_symm.keys()))

    # Compute path coverings based on coverage of symmetry-reduced state graph, even though we 
    # select covering paths from the full state graph.
    COVERAGE_PCT = args.coverage_pct
    print(f"Computing path covering with {COVERAGE_PCT*100}% coverage.")
    covering_paths = cover.compute_path_coverings(G, target_nodes_to_cover=set(node_map_symm.keys()), cvg_pct=COVERAGE_PCT)
    print(f"Computed {len(covering_paths)} covering paths (under SYMMETRY).")

    # Non-symmetric path coverings.
    # covering_paths = cover.compute_path_coverings(G, target_nodes_to_cover=set(node_map.keys()), cvg_pct=COVERAGE_PCT)
    # print(f"Computed {len(covering_paths)} covering paths.")

    end = time.time()

    traces = []
    for cpath in covering_paths:
        # print(cpath)
        # Convert path to list of edges.
        path_edges = []
        for i in range(len(cpath)-1):
            efrom, eto = cpath[i], cpath[i+1]
            path_edges.append((efrom, eto))
        # print("Path edges:", path_edges)
        # print("Path edges:", [edge_actions[e] for e in path_edges])
        trace = {"action":[]}
        for act in [edge_actions[e] for e in path_edges]:
            # print(act)
            # print(act[0], act[1])
            # act_params = act[1]
            # lines = make_wt_action(None, act["action"], act["actionParams"], None)
            # print("\n".join(lines))
            pre_state = [1,node_map[act["from"]]]
            post_state = [2,node_map[act["to"]]]
            trace["action"].append([
                pre_state,
                {
                    "context": act["actionParams"], 
                    "name": act["action"]
                },
                post_state
            ])
        traces.append(trace)
    gen_wt_test_from_traces(traces, compact=args.compact, cvg_pct=COVERAGE_PCT)
    print(f"Number of states in full model: {len(G.nodes())}")
    print(f"Computed path covering with {len(covering_paths)} paths.")
    print(f"Time taken to generate tests: {end-now:.2f} seconds.")


    # if not os.path.exists("model_traces"):
    #     os.makedirs("model_traces")

    # random.seed(14)

    # traces = []

    # for i in range(ntests):
    #     next_seed = random.randint(0, 1000000)
    #     gen_tla_model_trace(f"model_traces/trace_{i}.json", seed=next_seed)
    #     # print_trace(max_len=100)
    #     trace = json.load(open(f"model_traces/trace_{i}.json"))
    #     traces.append(trace)
    # gen_wt_test_from_traces(traces, max_len=100)
