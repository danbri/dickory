"""New source questions must not disappear behind a hard-coded old blocker."""
import unittest
from verify import complete_coverage_errors


class SourceQuestionGateTests(unittest.TestCase):
    def question_blockers(self, questions):
        return [e for e in complete_coverage_errors({"documents": [], "claims": []}, questions)
                if e.startswith("Source questions await expert adjudication:")]

    def test_every_pending_question_blocks(self):
        blockers = self.question_blockers([
            {"id": "Q-NEW-CLOSURE", "review_status": "pending_expert_review"},
            {"id": "Q-OLD", "review_status": "accepted"},
            {"id": "Q-MISSING-REVIEW", "status": "theorem_proved"},
        ])
        self.assertEqual(blockers, [
            "Source questions await expert adjudication: Q-MISSING-REVIEW, Q-NEW-CLOSURE"])

    def test_accepted_review_only_removes_question_blocker(self):
        questions = [{"id": "Q-REVIEWED", "review_status": "accepted"}]
        self.assertEqual(self.question_blockers(questions), [])
        self.assertIn("Published-artifact refinement has not been established",
                      complete_coverage_errors({"documents": [], "claims": []}, questions))


if __name__ == "__main__":
    unittest.main()
