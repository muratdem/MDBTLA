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

    def begin_transaction(self, tid, sess, readTs, ignorePrepare, res_expected):
        res,sret = None,None
        try:
            sess.begin_transaction(f'ignore_prepare={ignorePrepare},read_timestamp=' + self.timestamp_str(readTs));self.cursors[tid] = self.cursors[tid] = sess.open_cursor(self.uri, None)
        except wiredtiger.WiredTigerError as e:
            res = e
        self.assertEquals(res, res_expected)