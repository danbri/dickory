"""Guard the compiler-position to source-text boundary, especially Unicode."""
import unittest
from lean_sources import source_excerpt, expand_projection_sources


def pos(line, column):
    return {"line": line, "column": column}


class SourcePositions(unittest.TestCase):
    def test_columns_are_scalars_not_utf8_bytes_or_utf16_units(self):
        self.assertEqual(source_excerpt("α𝒢 → β\n", pos(1, 1), pos(1, 2)), "𝒢")
        self.assertEqual(source_excerpt("α𝒢 → β\n", pos(1, 3), pos(1, 4)), "→")

    def test_multiline_excerpt_preserves_newlines(self):
        self.assertEqual(source_excerpt("α𝒢 → β\r\nsecond\r\n", pos(1, 1), pos(2, 3)),
                         "𝒢 → β\r\nsec")

    def test_end_is_exclusive(self):
        self.assertEqual(source_excerpt("one\ntwo\n", pos(1, 0), pos(2, 0)), "one\n")

    def test_invalid_positions_fail_instead_of_showing_wrong_source(self):
        for start, end in [(pos(0, 0), pos(1, 1)), (pos(1, -1), pos(1, 1)),
                           (pos(1, 0), pos(1, 9)), (pos(1, 2), pos(1, 1)),
                           (pos(1, 1), pos(1, 1))]:
            with self.subTest(start=start, end=end), self.assertRaises(ValueError):
                source_excerpt("abc\n", start, end)


class ProjectionContext(unittest.TestCase):
    def fixture(self):
        text = "structure Model where\n  condition : α → Prop\n"
        parent = dict(name="Lab.Model", kind="inductive", path="Lab.lean",
                      start=pos(1, 0), end=pos(2, 22), code=text.rstrip("\n"))
        child = dict(name="Lab.Model.condition", kind="definition", path="Lab.lean",
                     start=pos(2, 2), end=pos(2, 11), code="condition")
        return {parent["name"]: parent, child["name"]: child}

    def test_name_only_field_exposes_condition_and_retains_exact_selection(self):
        rows = self.fixture()
        expand_projection_sources(rows)
        field = rows["Lab.Model.condition"]
        self.assertEqual(field["code"], rows["Lab.Model"]["code"])
        self.assertIn("condition : α → Prop", field["code"])
        self.assertEqual(field["source_context_declaration"], "Lab.Model")
        self.assertEqual(field["identifier_range"], {"start": pos(2, 2), "end": pos(2, 11)})
        self.assertEqual(field["start"], pos(1, 0))

    def test_complete_field_source_is_preserved(self):
        rows = self.fixture()
        rows["Lab.Model.condition"]["code"] = "condition : α → Prop"
        expand_projection_sources(rows)
        self.assertNotIn("source_context_declaration", rows["Lab.Model.condition"])
        self.assertEqual(rows["Lab.Model.condition"]["code"], "condition : α → Prop")

    def test_wrong_file_or_outside_range_does_not_borrow_unrelated_code(self):
        for change in ({"path": "Other.lean"}, {"start": pos(3, 2), "end": pos(3, 11)}):
            with self.subTest(change=change):
                rows = self.fixture()
                rows["Lab.Model.condition"].update(change)
                expand_projection_sources(rows)
                self.assertEqual(rows["Lab.Model.condition"]["code"], "condition")
                self.assertNotIn("source_context_declaration", rows["Lab.Model.condition"])


if __name__ == "__main__":
    unittest.main()
