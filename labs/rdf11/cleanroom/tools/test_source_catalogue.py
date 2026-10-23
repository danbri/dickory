import unittest
from source_catalogue import Locator


class SourceLocatorTests(unittest.TestCase):
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
