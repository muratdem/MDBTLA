import json

def make_wt_action(pre_state, action_name, action_args, post_state):
    print(action_name)
    tid = action_args['tid']
    wt_action_name = action_name.lower().replace("mdbtxn", "transaction_")
    err_code = post_state[1]['txnStatus'][tid]
    txn_cursor = f"cursor_{tid}"
    print(err_code)
    txn_session = f"sess_{tid}"
    if action_name == "MDBTxnStart":
        wt_action_name = f"{txn_session}.begin_transaction('read_timestamp=' + self.timestamp_str({action_args['readTs']}));{txn_cursor} = sess_t1.open_cursor(self.uri, None)"
    if action_name == "MDBTxnWrite":
        wt_action_name = f"{txn_cursor}.set_key(\"{action_args['k']}\");{txn_cursor}.set_value(\"{action_args['v']}\");{txn_cursor}.insert()"
    if action_name == "MDBTxnRead":
        wt_action_name = f"{txn_cursor}.set_key(\"{action_args['k']}\");sret = {txn_cursor}.search()\n"
        if action_args['v'] == "NoValue":
            wt_action_name += f"    self.assertEquals(sret, wiredtiger.WT_NOTFOUND)"
        else:
            wt_action_name += f"    self.assertEquals({txn_cursor}.get_value(), \"{action_args['v']}\")"
    if action_name == "MDBTxnPrepare":
        wt_action_name = f"{txn_session}.prepare_transaction('prepare_timestamp=' + self.timestamp_str({action_args['prepareTs']}))"
    if action_name == "MDBTxnCommit":
        wt_action_name = f"{txn_session}.commit_transaction('commit_timestamp=' + self.timestamp_str({action_args['commitTs']}))"
    if action_name == "MDBTxnAbort":
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
    return "\n".join(lines)

def print_trace():
    with open('trace.json', 'r') as f:
        trace = json.load(f)

    wt_actions = []
        
    # Print each action in the trace
    for action in trace['action']:
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

    print("\n-----\nWT Actions:")

    # Open a separate session for all transactions.
    txns = ["t1", "t2"]

    f = open("trace_actions.txt", "w")

    for t in txns:
        out = f"sess_{t} = conn.open_session()\n"
        print(out)
        f.write(out)
    print("")
    f.write("\n")
    for i, a in enumerate(wt_actions):
        action_label = f"## Action {i}: {trace['action'][i][1]['name']}, {[trace['action'][i][1]['context'][p] for p in trace['action'][i][1]['parameters']]}"
        print(action_label)
        print(a)
        print("")
        f.write(action_label)
        f.write("\n")
        f.write(a)  
        f.write("\n")
    f.close()

if __name__ == '__main__':
    print_trace()