import tempfile
from pathlib import Path
import unittest
from hierarchy_evidence_support import LOCAL, instrument, restore_snapshot


class Controls(unittest.TestCase):
    def test_each_scope_and_negative(self):
        text = (LOCAL + '\nprivate theorem x : True := by\n  trivial\n') * 2
        positive, n = instrument(text)
        negative, m = instrument(text, negative=True)
        self.assertEqual((n, m), (2, 2))
        self.assertEqual(positive.count('run_tac'), 2)
        self.assertNotIn(LOCAL, negative)
        self.assertEqual(negative.count('run_tac'), 2)

    def test_unknown_or_uninstrumentable_attribute_fails(self):
        for text in ('@[simp] theorem x : True := by trivial', LOCAL + '\ndef x := 1'):
            with self.assertRaises(AssertionError):
                instrument(text)

    def test_readonly_hardlink_and_symlink_destinations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            src, dst = root / 'src', root / 'dst'
            src.mkdir()
            dst.mkdir()
            original = root / 'cache'
            original.write_text('cache')
            original.chmod(0o444)
            (dst / 'hard').hardlink_to(original)
            (dst / 'sym').symlink_to(original)
            for name in ('hard', 'sym'):
                (src / name).write_text('revision')
            restore_snapshot(src, dst)
            self.assertEqual(original.read_text(), 'cache')
            for name in ('hard', 'sym'):
                self.assertEqual((dst / name).read_text(), 'revision')
                self.assertFalse((dst / name).is_symlink())
                self.assertNotEqual((dst / name).stat().st_ino, original.stat().st_ino)


if __name__ == '__main__':
    unittest.main()
