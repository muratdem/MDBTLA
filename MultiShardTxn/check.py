#
# Simple runner script for TLC with JSON model config that allows command line overrides
# of parameters.
#
# 
# Usage example:
#   
#   python3 check.py --constants "Keys={k1,k2,k3}" "Shard={s1,s2}" --invariants SnapshotIsolation RepeatableReadIsolation --tlc_jar /usr/local/bin/tla2tools.jar
#

import subprocess
import json
import argparse


def make_config_file(config_obj):
    #create TLC config file for each parameter in config json.
    cfg_file_text = ""

    if "init" in config_obj and "next" in config_obj:
        cfg_file_text += f"INIT {config_obj['init']}\n"
        cfg_file_text += f"NEXT {config_obj['next']}\n"

    if "constants" in config_obj:
        cfg_file_text += "CONSTANTS\n"
        for constant in config_obj["constants"]:
            cfg_file_text += f"  {constant} = {config_obj['constants'][constant]}\n"

    if "invariants" in config_obj:
        cfg_file_text += "INVARIANTS\n"
        for invariant in config_obj["invariants"]:
            cfg_file_text += f"  {invariant}\n"

    return(cfg_file_text)



# Add command line arguments parser to allow overriding the config file parameters.
parser = argparse.ArgumentParser()
# allow overriding of constants as multiple --constant key-val pairs
parser.add_argument("--constants", nargs="+", help="constants to override")
parser.add_argument("--invariants", nargs="+", help="invariants to override")
parser.add_argument("--tlc_args", nargs="+", help="invariants to override", type=str, default="")
parser.add_argument("--tlc_jar", nargs="+", help="invariants to override", default="/usr/local/bin/tla2tools.jar")

# extract constants args if they exist.
args = parser.parse_args()
print(args)

#  open and load JSON config file.
config_file = "MultiShardTxn.config.json"
with open(config_file) as f:
    config = json.load(f)

# Override constants in config file with command line args if given.
for constant in args.constants:
    cname = constant.split("=")[0]
    cval = constant.split("=")[1]
    config["constants"][cname] = cval

# Override invariants in config file with command line args if given.
if args.invariants:
    config["invariants"] = args.invariants

cfg_text = make_config_file(config)
print(cfg_text)
fout = open("MultiShardTxn_gen.cfg", "w")
fout.write(cfg_text)
fout.close()

# Run TLC model checker via command line with subprocess.
tlc_jar=args.tlc_jar
tlc_args = (["-" + a for a in args.tlc_args])
args = ["java", "-cp", tlc_jar, "tlc2.TLC"] + tlc_args + ["-config", "MultiShardTxn_gen.cfg", "MultiShardTxn"]
print(args)
print(" ".join(args))
ret = subprocess.run(args, shell=False)
