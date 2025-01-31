import json
import os
import random
import argparse

WT_TEST_TEMPLATE = """
# [TEST_TAGS]
# transactions
# [END_TAGS]

import wttest
import wiredtiger
from wtscenario import make_scenarios

class test_txn_mbt(wttest.WiredTigerTestCase):

    def check_action(self, action_fn, expected_res, expected_exception):
        res = None
        try:
            action_fn()
        except wiredtiger.WiredTigerError as e:
            res = e
        self.assertEquals(res, None)
        self.assertTrue(wiredtiger.wiredtiger_strerror(expected_exception) in str(res))
"""

WT_TEST_FN_TEMPLATE = """
    def test_trace_1(self):
        key_format,value_format = "S","S"
        self.uri = 'table:test_txn01'
        self.session.create(self.uri, 'key_format=' + key_format + ',value_format=' + value_format)
        conn = self.conn
"""

def make_wt_action(pre_state, action_name, action_args, post_state):
    print(action_name)
    tid = ""
    err_code = None
    if "tid" in action_args:
        tid = action_args['tid']
        err_code = post_state[1]['txnStatus'][tid]
    wt_action_name = action_name.lower().replace("mdbtxn", "transaction_")
    txn_cursor = f"self.cursor_{tid}"
    # print(err_code)
    txn_session = f"sess_{tid}"
    if action_name == "StartTransaction":
        wt_action_name = f"{txn_session}.begin_transaction('read_timestamp=' + self.timestamp_str({action_args['readTs']}));{txn_cursor} = {txn_session}.open_cursor(self.uri, None)"
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
        lines.append("self.assertEqual(wiredtiger.WT_NOTFOUND, sret)")
    elif err_code == "WT_PREPARE_CONFLICT":
        lines.append("self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_PREPARE_CONFLICT) in str(res))")
    else:
        lines.append("self.assertEquals(res, None)")
        if action_name == "TransactionRemove":
            lines.append("self.assertEquals(0, sret)")
    # lines = [
        # "self.check_action(lambda: " + wt_action_name + ", " + str(res_expected) + ", " + str(exception_str) + ")"
    # ]

    return lines

def gen_wt_test_from_traces(traces, max_len=1000):
    print("\n-----\nWT Actions:")

    # Open a separate session for all transactions.
    txns = ["t1", "t2", "t3"]

    f = open("test_txn_model_traces.py", "w")
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
            
            print("\nAction:", transition['name'])
            # print("Initial State:", init_state)
            print("Parameters:", action_args)
            # print("Parameters:", transition['parameters'])
            # print("Context:", transition['context'])
            # print("Final State:", final_state)
            wt_actions.append(make_wt_action(pre_state, transition['name'], action_args, post_state))


        f.write(WT_TEST_FN_TEMPLATE.replace("test_trace_1", f"test_trace_{i}"))

        for t in txns:
            out = tab(2) + f"sess_{t} = conn.open_session()\n"
            print(out)
            f.write(out)
        print("")
        f.write("\n")
        action_labels = []
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
            print(action_ctx)
            action_params_str = ','.join([str(action_ctx[p]) for p in params])
            print(post_state)
            txn_post_state = None
            tid = None
            if "tid" in action_ctx:
                tid = action_ctx['tid']
                txn_post_state = post_state['txnStatus'][tid]
            action_label = f"### Action {i+1}: {action_name}({action_params_str}) res:{txn_post_state}"
            action_labels.append(tab(2) +action_label)
            print(action_label)
            print(a)
            print("")
            test_lines.append(tab(2) + action_label)
            test_lines.append("\n")
            for l in a:
                test_lines.append(tab(2) + l + "\n")
            test_lines.append("\n")
        f.write("\n")
        f.write("\n".join(action_labels))
        f.write("\n\n\n")
        f.writelines(test_lines)
    f.close()

def gen_tla_model_trace(json_trace="trace.json", seed=0):
    tlc = "java -cp /usr/local/bin/tla2tools-v1.8.jar tlc2.TLC -noGenerateSpecTE"
    spec = "MDBTest"
    cmd = f"{tlc} -seed {seed} -dumpTrace json {json_trace} -simulate -workers 1 -cleanup -deadlock {spec}.tla"
    # print(cmd)
    os.system(cmd)

if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument('--ntests', type=int, default=50, help='Number of test traces to generate')
    args = parser.parse_args()
    ntests = args.ntests

    if not os.path.exists("model_traces"):
        os.makedirs("model_traces")

    random.seed(14)

    traces = []

    for i in range(ntests):
        next_seed = random.randint(0, 1000000)
        gen_tla_model_trace(f"model_traces/trace_{i}.json", seed=next_seed)
        # print_trace(max_len=100)
        trace = json.load(open(f"model_traces/trace_{i}.json"))
        traces.append(trace)
    gen_wt_test_from_traces(traces, max_len=100)
