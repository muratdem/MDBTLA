

import subprocess

def compute_permissiveness(config_name):
    tlc="java -cp tla2tools-txn-ops-project.jar tlc2.TLC"
    cmd=f"{tlc} -deadlock -workers 10 -config {config_name}.cfg -fp 1 MCMultiShardTxn.tla | tee logout"
    subprocess.run(cmd, shell=True)
    subprocess.run(f"grep 'fpl' logout | sort | uniq > permissiveness_{config_name}.txt", shell=True)

    lines = open(f"permissiveness_{config_name}.txt").read().splitlines()

    uniq_fps = {}
    for line in lines:
        elems = line.split("$")
        fp = elems[1]
        uniq_fps[fp] = elems[2]

    # print(config_name, len(uniq_fps))
    return uniq_fps

def strict_subset_ordered(a, b):
    return set(a.keys()).issubset(set(b.keys())) and not set(b.keys()).issubset(set(a.keys()))

schedules_prepare = compute_permissiveness("MCMultiShardTxn_RC_with_prepare_block")
schedules_no_prepare = compute_permissiveness("MCMultiShardTxn_RC_no_prepare_block")
schedules_no_prepare_no_ww = compute_permissiveness("MCMultiShardTxn_RC_no_prepare_block_or_ww")

# Ensure one of these schedules is a strict subset of the other.
ordered1 = strict_subset_ordered(schedules_prepare, schedules_no_prepare)
ordered2 = strict_subset_ordered(schedules_no_prepare, schedules_no_prepare_no_ww)

# assert ordered1 or ordered2

diff = set(schedules_no_prepare.keys()).symmetric_difference(set(schedules_prepare.keys()))
print(len(diff))
print(diff)
for d in diff:
    if d in schedules_prepare:
        print("schedules_prepare")
        print(d, schedules_prepare[d])
    if d in schedules_no_prepare:
        print("schedules_no_prepare")
        print(d, schedules_no_prepare[d])

diff = set(schedules_no_prepare_no_ww.keys()).symmetric_difference(set(schedules_no_prepare.keys()))
print(len(diff))
print(diff)
for d in diff:
    if d in schedules_no_prepare_no_ww:
        print("schedules_no_prepare_no_ww")
        print(d, schedules_no_prepare_no_ww[d])
    if d in schedules_no_prepare:
        print("schedules_no_prepare")
        print(d, schedules_no_prepare[d])

print("schedules_prepare", len(schedules_prepare))
print("schedules_no_prepare", len(schedules_no_prepare))
print("schedules_no_prepare_no_ww", len(schedules_no_prepare_no_ww))

print("ordered1", ordered1)
print("ordered2", ordered2)

# -2478145200821578246 
# (t1 :> <<[op |-> "read", key |-> k2, value |-> NoValue], [op |-> "read", key |-> k2, value |-> t2]>> @@ 
#  t2 :> <<[op |-> "read", key |-> k1, value |-> NoValue], [op |-> "write", key |-> k2, value |-> t2]>>)


# 2793947217171754682 (
# t1 :> <<[op |-> "read", key |-> k2, value |-> NoValue], [op |-> "read", key |-> k2, value |-> t2]>> @@ 
# t2 :> <<[op |-> "write", key |-> k2, value |-> t2]>>
# )