import json

def make_wt_action(action_name, action_args):
    print(action_name)
    wt_action_name = action_name.lower().replace("mdbtxn", "transaction_")
    txn_session = f"sess_{action_args['tid']}"
    if action_name == "MDBTxnStart":
        wt_action_name = f"{txn_session}.begin_transaction('read_timestamp=' + self.timestamp_str({action_args['readTs']}))"
    if action_name == "MDBTxnWrite":
        wt_action_name = f"{txn_session}.insert({action_args['k']},{action_args['v']})"
    if action_name == "MDBTxnRead":
        wt_action_name = f"{txn_session}.read({action_args['k']})"
    if action_name == "MDBTxnPrepare":
        wt_action_name = f"{txn_session}.prepare_transaction('prepare_timestamp=' + self.timestamp_str({action_args['prepareTs']}))"
    if action_name == "MDBTxnCommit":
        wt_action_name = f"{txn_session}.commit_transaction('commit_timestamp=' + self.timestamp_str({action_args['commitTs']}))"
    # wt_args = [str(action_args[p]) for p in action_args]
    return f"{wt_action_name}"

def print_trace():
    with open('trace.json', 'r') as f:
        trace = json.load(f)

    wt_actions = []
        
    # Print each action in the trace
    for action in trace['action']:
        # Each action has 3 elements: initial state, transition info, final state
        # init_state = action[0]
        transition = action[1] 
        action_args = transition['context']
        # final_state = action[2]
        
        print("\nAction:", transition['name'])
        # print("Initial State:", init_state)
        print("Parameters:", action_args)
        # print("Parameters:", transition['parameters'])
        # print("Context:", transition['context'])
        # print("Final State:", final_state)
        wt_actions.append(make_wt_action(transition['name'], action_args))

    print("\n-----\nWT Actions:")

    # Open a separate session for all transactions.
    txns = ["t1", "t2"]
    for t in txns:
        print(f"sess_{t} = conn.open_session()")
    for a in wt_actions:
        print(a)
if __name__ == '__main__':
    print_trace()
