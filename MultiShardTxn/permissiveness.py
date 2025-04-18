

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

schedules_prepare = compute_permissiveness("MCMultiShardTxn_RC_with_prepare_block")
schedules_no_prepare = compute_permissiveness("MCMultiShardTxn_RC_no_prepare_block")

print("schedules_prepare", len(schedules_prepare))
print("schedules_no_prepare", len(schedules_no_prepare))

diff = schedules_no_prepare.keys().symmetric_difference(schedules_prepare.keys())
print(len(diff))
print(diff)
for d in diff:
    if d in schedules_prepare:
        print("schedules_prepare")
        print(d, schedules_prepare[d])
    if d in schedules_no_prepare:
        print("schedules_no_prepare")
        print(d, schedules_no_prepare[d])



