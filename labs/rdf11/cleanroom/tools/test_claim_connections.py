import unittest
from claim_connections import claim_connections

class ConnectionTests(unittest.TestCase):
    def test_paths_shared_bindings_and_cycles(self):
        def claim(cid,*names):return {'id':cid,'cleanroom_mapping':{'bindings':[{'lean':n} for n in names]}}
        claims=[claim('A','a'),claim('B','b'),claim('C','b'),claim('D','d')]
        declarations={'a':{'dependencies':['helper']},'helper':{'dependencies':['b']},'b':{'dependencies':['helper']},'d':{'dependencies':[]}}
        result=claim_connections(claims,declarations)
        self.assertEqual(result['A']['uses'][0],{'claim':'B','path':['a','helper','b']})
        self.assertEqual(result['B']['used_by'][0]['claim'],'A')
        self.assertEqual(result['B']['shared'],[{'claim':'C','declarations':['b']}])
        self.assertEqual(result['D'],{'uses':[],'used_by':[],'shared':[]})

if __name__=='__main__':unittest.main()
