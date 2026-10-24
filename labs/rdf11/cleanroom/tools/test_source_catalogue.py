import json
import unittest
from source_catalogue import Locator, produce


class SourceLocatorTests(unittest.TestCase):
    def test_every_document_disposition_is_in_the_lean_certificate(self):
        generated = produce()
        catalogue = json.loads(generated['catalogue/claims.json'])
        line = next(line for line in generated['Audit/Snapshot.lean'].splitlines()
                    if line.startswith('def ids : List String := '))
        ids = set(json.loads(line.split(' := ', 1)[1]))
        for doc in catalogue['documents']:
            self.assertIn('UNRESOLVED-' + doc['id'], ids)
            for atom in doc['atoms']:
                self.assertTrue(set(atom['refs']) <= ids)

    def test_exact_connective_does_not_select_surrounding_prose(self):
        locator = Locator('<section id="r"><p>A does not entail B.</p>'
                          '<p>does not entail</p></section>')
        selector = dict(id="connective", tag="p", text="does not entail", within_section="r")
        with self.assertRaisesRegex(ValueError, "found 2"):
            locator.select(selector)
        node = locator.select(dict(selector, exact_text=True))
        self.assertEqual(node["text"], "does not entail")
        self.assertEqual(locator.source[node["start"]:node["end"]], '<p>does not entail</p>')


if __name__ == "__main__":
    unittest.main()
