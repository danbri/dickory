"""Guard the compiler-position to source-text boundary, especially Unicode."""
import unittest
from lean_sources import source_excerpt


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


if __name__ == "__main__":
    unittest.main()
