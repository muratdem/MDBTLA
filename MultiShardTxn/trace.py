import json
import os

WT_TEST_TEMPLATE = """
# [TEST_TAGS]
# transactions
# [END_TAGS]

import wttest
import wiredtiger
from wtscenario import make_scenarios

# test_txn01.py
#    Transactions: basic functionality
class test_txn01(wttest.WiredTigerTestCase):

    def test_trace_1(self):
        key_format = "S"
        value_format = "S"
        self.uri = 'table:test_txn01'
        self.session.create(self.uri,
            'key_format=' + key_format +
            ',value_format=' + value_format)

        conn = self.conn
"""

WT_TEST_FN_TEMPLATE = """
    def test_trace_1(self):
        key_format = "S"
        value_format = "S"
        self.uri = 'table:test_txn01'
        self.session.create(self.uri,
            'key_format=' + key_format +
            ',value_format=' + value_format)

        conn = self.conn
"""

def make_wt_action(pre_state, action_name, action_args, post_state):
    print(action_name)
    tid = action_args['tid']
    wt_action_name = action_name.lower().replace("mdbtxn", "transaction_")
    err_code = post_state[1]['txnStatus'][tid]
    txn_cursor = f"cursor_{tid}"
    print(err_code)
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
    # wt_args = [str(action_args[p]) for p in action_args]
    # return f"{wt_action_name}, {err_code}"
    lines = [
        "res = None",
        "try:",
        f"    {wt_action_name}",
        "except wiredtiger.WiredTigerError as e:",
        "    res = e"
    ]
    if err_code == "WT_ROLLBACK":
        lines.append("self.assertNotEqual(res, None)")
        lines.append("self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_ROLLBACK) in str(e))")
    else:
        lines.append("self.assertEquals(res, None)")
    return lines

def gen_wt_test_from_traces(traces, max_len=1000):
    print("\n-----\nWT Actions:")

    # Open a separate session for all transactions.
    txns = ["t1", "t2"]

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
        for i, a in enumerate(wt_actions):
            action_name = trace['action'][i][1]['name']
            action_ctx = trace['action'][i][1]['context']
            params = trace['action'][i][1]['parameters']
            print(action_ctx)
            action_params_str = ','.join([str(action_ctx[p]) for p in params])
            action_label = f"### Action {i+1}: {action_name}({action_params_str})"
            print(action_label)
            print(a)
            print("")
            f.write(tab(2) + action_label)
            f.write("\n")
            for l in a:
                f.write(tab(2) + l + "\n")  
            f.write("\n")
    f.close()

def gen_tla_model_trace(json_trace="trace.json"):
    tlc = "java -cp /usr/local/bin/tla2tools-v1.8.jar tlc2.TLC -noGenerateSpecTE"
    spec = "MDBTest"
    cmd = f"{tlc} -dumpTrace json {json_trace} -simulate -workers 10 -cleanup -deadlock {spec}.tla"
    # print(cmd)
    os.system(cmd)

if __name__ == '__main__':
    if not os.path.exists("model_traces"):
        os.makedirs("model_traces")
    traces = []
    for i in range(8):
        gen_tla_model_trace(f"model_traces/trace_{i}.json")
        # print_trace(max_len=100)
        trace = json.load(open(f"model_traces/trace_{i}.json"))
        traces.append(trace)
    gen_wt_test_from_traces(traces, max_len=100)
