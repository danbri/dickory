import unittest
from rendered_source import reading_copy
from source_catalogue import Locator, produce, ROOT
import json

class ReadingTests(unittest.TestCase):
    def test_unicode_offsets_and_nested_associations(self):
        raw='<div>😀\r\n<p id="x">A &amp; B</p></div>'
        p=raw.index('<p')
        result=reading_copy(raw,[{'start':0,'id':'outer'},{'start':p,'id':'inner'}])
        self.assertIn('data-passages="outer"',result)
        self.assertIn('id="x" data-passages="inner">A &amp; B',result)
        self.assertIn('😀\r\n',result)
    def test_passive_copy(self):
        raw='<script>alert(1)</script><p onclick="bad()">ok<img src="https://x/" alt="picture"><a href="javascript:bad()">link</a><iframe src="x"></iframe></p>'
        result=reading_copy(raw,[])
        self.assertNotIn('alert',result)
        self.assertNotIn('onclick',result)
        self.assertNotIn('src=',result)
        self.assertNotIn('javascript',result)
        self.assertNotIn('iframe',result)
        self.assertIn('okpicture',result)
    def test_unattachable_passage_fails(self):
        with self.assertRaises(ValueError):reading_copy('<p>text</p>',[{'start':4,'id':'bad'}])
    def test_all_actual_passages_attach_once(self):
        c=json.loads(produce()['catalogue/claims.json'])
        for d in c['documents']:
            ps=[p for p in c['passages'] if p['source']==d['id']]
            raw=(ROOT/d['path']).read_bytes().decode('utf-8')
            copy=reading_copy(raw,ps)
            nodes=Locator(copy).nodes
            attached=[pid for n in nodes for pid in n['attrs'].get('data-passages','').split()]
            self.assertCountEqual(attached,[p['id'] for p in ps])

if __name__=='__main__':unittest.main()
