from hypothesis.strategies import integers, lists, sampled_from
from hypothesis import note, settings, assume
from hypothesis.stateful import RuleBasedStateMachine, rule, precondition, invariant


class DieHardProblem(RuleBasedStateMachine):
    TXN_IDS = ["t1", "t2"]
    KEYS = ["k1", "k2"]

    log = []
    txnSnapshots = {}
    runningTxns = set()

    @rule(tid=sampled_from(TXN_IDS), readTs=integers(min_value=0, max_value=5))
    def start_transaction(self, tid, readTs):
        self.txnSnapshots[tid] = {"readTs": readTs, "data": {k:None for k in self.KEYS}}
        self.runningTxns.add(tid)

    @rule(tid=sampled_from(TXN_IDS), key=sampled_from(KEYS))
    # @precondition(lambda self: tid in self.runningTxns)
    def transaction_write(self, tid, key):
        assume(tid in self.runningTxns) # using 'assume' vs. 'precondition' (??)
        self.txnSnapshots[tid]["data"][key] = tid

    # @rule()
    # def pour_small_into_big(self):
    #     old_big = self.big
    #     self.big = min(5, self.big + self.small)
    #     self.small = self.small - (self.big - old_big)

    # @rule()
    # def pour_big_into_small(self):
    #     old_small = self.small
    #     self.small = min(3, self.small + self.big)
    #     self.big = self.big - (self.small - old_small)

    # @invariant()
    # def physics_of_jugs(self):
    #     assert 0 <= self.small <= 3
    #     assert 0 <= self.big <= 5

    # @invariant()
    # def die_hard_problem_not_solved(self):
    #     # note("> small: {s} big: {b}".format(s=self.small, b=self.big))
    #     assert len(self.txnSnapshots.keys()) == 0


# The default of 200 is sometimes not enough for Hypothesis to find
# a falsifying example.
# with settings(max_examples=2000):
# for i in range(1000):
#     DieHardTest = DieHardProblem.TestCase
#     DieHardTest = DieHardProblem.TestCase
#     DieHardTest = DieHardProblem.TestCase
#     DieHardTest = DieHardProblem.TestCase
DieHardTest = DieHardProblem.TestCase
DieHardTest.settings = settings(
    max_examples=5, stateful_step_count=100
)
import unittest
# Or just run with pytest's unittest support
if __name__ == "__main__":
    unittest.main()