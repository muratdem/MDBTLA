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

    def evict(self, k):
        evict_cursor = self.session.open_cursor(self.uri, None, "debug=(release_evict)")
        self.session.begin_transaction()
        evict_cursor.set_key(k)
        evict_cursor.search()
        evict_cursor.reset()
        evict_cursor.close()
        self.session.rollback_transaction()

    def debug_info(self):
        with self.expectedStdoutPattern('transaction state dump'):
            self.conn.debug_info('txn')

    def test_setup(self):
        key_format,value_format = "S","S"
        self.uri = 'table:test_txn01'
        self.session.create(self.uri, 'key_format=' + key_format + ',value_format=' + value_format)
        conn = self.conn
        self.cursors = {}
        self.conn.set_timestamp('oldest_timestamp='+self.timestamp_str(1))

    def check_timestamps(self, all_durable=None, stable_ts=None, oldest_ts=None):
        if all_durable is not None:
            self.assertTimestampsEqual(self.conn.query_timestamp('get=all_durable'), str(all_durable))
        if stable_ts is not None:
            self.assertTimestampsEqual(self.conn.query_timestamp('get=stable_timestamp'), str(stable_ts))
        if oldest_ts is not None:
            self.assertTimestampsEqual(self.conn.query_timestamp('get=oldest_timestamp'), str(oldest_ts))

    def check_response(self, res, err_code, sret=None):
        if err_code == "WT_ROLLBACK":
            self.assertNotEqual(res, None)
            self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_ROLLBACK) in str(res))
        elif err_code == "WT_NOTFOUND":
            # lines.append("self.assertEqual(res, None)")
            self.assertEqual(sret, wiredtiger.WT_NOTFOUND)
        elif err_code == "WT_PREPARE_CONFLICT":
            self.assertTrue(wiredtiger.wiredtiger_strerror(wiredtiger.WT_PREPARE_CONFLICT) in str(res))
        else:
            self.assertEquals(res, None)
            # if action_name == "TransactionRemove":
                # lines.append("self.assertEquals(sret, 0)")

    def begin_transaction(self, tid, sess, readTs, ignorePrepare, res_expected, err_code):
        res,sret = None,None
        try:
            sess.begin_transaction(f'ignore_prepare={ignorePrepare},read_timestamp=' + self.timestamp_str(readTs));self.cursors[tid] = self.cursors[tid] = sess.open_cursor(self.uri, None)
            self.assertTimestampsEqual(sess.query_timestamp('get=read'), str(readTs))
        except wiredtiger.WiredTigerError as e:
            res = e
        # self.assertEquals(res, res_expected)
        self.check_response(res, err_code)

    def transaction_write(self, tid, k, res_expected, err_code):
        res,sret = None,None
        try:
            self.cursors[tid].set_key(k);self.cursors[tid].set_value(tid);self.cursors[tid].insert()
        except wiredtiger.WiredTigerError as e:
            res = e
        # self.assertEquals(res, res_expected)
        self.check_response(res, err_code)

    def transaction_read(self, tid, k, v, res_expected, err_code):
        res,sret = None,None
        try:
            self.cursors[tid].set_key(k);sret = self.cursors[tid].search()
                # self.assertEquals(res, None)
            if v == "NoValue":
                self.assertEquals(sret, wiredtiger.WT_NOTFOUND)
            else:
                # self.assertEquals(res, res_expected)
                self.assertEquals(self.cursors[tid].get_value(), v)
        except wiredtiger.WiredTigerError as e:
            res = e
        self.check_response(res, err_code, sret=sret)

    def transaction_remove(self, tid, k, res_expected, err_code):
        res,sret = None,None
        try:
            self.cursors[tid].set_key(k);sret = self.cursors[tid].remove()
        except wiredtiger.WiredTigerError as e:
            res = e
        # self.assertEquals(res, None)
        # self.assertEquals(sret, 0)
        self.check_response(res, err_code, sret=sret)


    def commit_transaction(self, sess, tid, commitTs, res_expected, err_code):
        res,sret = None,None
        try:
            # Set timestamp as well explicitly to cover that API.
            sess.timestamp_transaction_uint(wiredtiger.WT_TS_TXN_TYPE_COMMIT, commitTs)
            self.assertTimestampsEqual(sess.query_timestamp('get=commit'), str(commitTs))
            sess.commit_transaction('commit_timestamp=' + self.timestamp_str(commitTs))
        except wiredtiger.WiredTigerError as e:
            res = e
        # self.assertEquals(res, res_expected)
        self.check_response(res, err_code)
    
    def abort_transaction(self, sess, tid, res_expected, err_code):
        res,sret = None,None
        try:
            sess.rollback_transaction()
        except wiredtiger.WiredTigerError as e:
            res = e
        self.assertEquals(res, None)

    def prepare_transaction(self, sess, prepareTs, res_expected, err_code):
        res,sret = None,None
        try:
            sess.prepare_transaction('prepare_timestamp=' + self.timestamp_str(prepareTs))
            self.assertTimestampsEqual(sess.query_timestamp('get=prepare'), str(prepareTs))
        except wiredtiger.WiredTigerError as e:
            res = e
        # self.assertEquals(res, None)
        self.check_response(res, err_code)

    def commit_prepared_transaction(self, sess, commitTs, durableTs, res_expected, err_code):
        res,sret = None,None
        try:
            sess.commit_transaction('commit_timestamp=' + self.timestamp_str(commitTs) + ',durable_timestamp=' + self.timestamp_str(durableTs))
        except wiredtiger.WiredTigerError as e:
            res = e
        self.check_response(res, err_code)

    # TODO: Make use of this.
    def set_oldest_timestamp(self, ts, err_code):
        try:
            self.conn.set_timestamp('oldest_timestamp='+self.timestamp_str(ts))
        except wiredtiger.WiredTigerError as e:
            res = e
        self.check_response(res, err_code)
