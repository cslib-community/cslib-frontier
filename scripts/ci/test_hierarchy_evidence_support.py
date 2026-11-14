import tempfile
from pathlib import Path
import unittest
from hierarchy_evidence_support import LOCAL, attribute_control_passed, instrument, restore_snapshot, scoped_control_passed, attribute_matrix_complete, registration_counts


class Controls(unittest.TestCase):
    def test_each_scope_and_negative(self):
        text = (LOCAL + '\nprivate theorem x : True := by\n  trivial\n') * 2
        positive, n = instrument(text)
        negative, m = instrument(text, negative=True)
        self.assertEqual((n, m), (2, 2))
        self.assertEqual(positive.count('run_tac'), 2)
        self.assertNotIn(LOCAL, negative)
        self.assertEqual(negative.count('run_tac'), 2)
        self.assertEqual(positive.count('run_cmd'), 2)
        self.assertEqual(positive.count('initialize hierarchyEvidence5530Baseline'), 1)
        self.assertEqual(positive.replace(LOCAL, ''), negative)
        self.assertEqual(positive.count('hierarchyEvidence5530Baseline.set counts'), 2)
        self.assertIn('COUNTS 1 baseline', positive)
        self.assertIn('COUNTS 2 baseline', positive)
        self.assertIn('COUNTS 2 inside', positive)
        self.assertEqual(positive.count('(ts.filter (· == t)).size'), 2)

    def test_unknown_or_uninstrumentable_attribute_fails(self):
        for text in ('@[simp] theorem x : True := by trivial', LOCAL + '\ndef x := 1'):
            with self.assertRaises(AssertionError):
                instrument(text)

    def test_attribute_messages_exclude_warning_source_echoes(self):
        echo = ('Client.lean:2:1: warning: unused tactic\n'
                '  Lean.logInfo "HIERARCHY_ATTRIBUTE_PRESENT"\n'
                '  unless found do throwError "HIERARCHY_ATTRIBUTE_MISSING"\n')
        self.assertTrue(attribute_control_passed(0, echo + 'HIERARCHY_ATTRIBUTE_PRESENT\n', 1))
        self.assertFalse(attribute_control_passed(0, echo, 1))
        self.assertFalse(attribute_control_passed(1, 'HIERARCHY_ATTRIBUTE_PRESENT\n', 1))
        self.assertFalse(attribute_control_passed(1, echo, 1, True))
        missing = 'Client.lean:3:2: error: HIERARCHY_ATTRIBUTE_MISSING\n'
        self.assertTrue(attribute_control_passed(1, echo + missing * 2, 2, True))
        self.assertFalse(attribute_control_passed(0, missing, 1, True))
        self.assertFalse(attribute_control_passed(1, missing, 2, True))
        self.assertFalse(attribute_control_passed(1, missing * 2, 1, True))
        self.assertFalse(attribute_control_passed(0, 'HIERARCHY_ATTRIBUTE_PRESENT\n' * 2, 1))

    @staticmethod
    def scope_log(baseline, inside, scope=1, negative=False):
        return (f'HIERARCHY_ATTRIBUTE_COUNTS {scope} baseline {baseline[0]} {baseline[1]}\n'
                f'HIERARCHY_ATTRIBUTE_COUNTS {scope} inside {inside[0]} {inside[1]}\n'
                + ('Client.lean:3:2: error: HIERARCHY_ATTRIBUTE_MISSING\n' if negative
                   else 'HIERARCHY_ATTRIBUTE_PRESENT\n'))

    def test_registration_deltas(self):
        for baseline in ([0, 0], [1, 1], [0, 3]):
            positive = [n + 1 for n in baseline]
            log = self.scope_log(baseline, positive)
            self.assertTrue(scoped_control_passed(0, log, 1))
            negative = self.scope_log(baseline, baseline, negative=True)
            self.assertTrue(scoped_control_passed(1, negative, 1, True))
            # The old imported-membership false positive must fail even with PRESENT.
            self.assertFalse(scoped_control_passed(0, self.scope_log(baseline, baseline), 1))
            for inside in ([positive[0], baseline[1]], [positive[0] + 1, positive[1]]):
                self.assertFalse(scoped_control_passed(0, self.scope_log(baseline, inside), 1))
                self.assertFalse(scoped_control_passed(
                    1, self.scope_log(baseline, inside, negative=True), 1, True))
            for malformed in (log.replace('baseline', 'ignored'), log + log,
                              log.replace(' 1 inside ', ' 2 inside ')):
                self.assertFalse(scoped_control_passed(0, malformed, 1))
            self.assertFalse(scoped_control_passed(1, log, 1))
            self.assertFalse(scoped_control_passed(0, negative, 1, True))

    def test_complete_matrix_and_independent_nexp_baselines(self):
        variants = ['before', '5494', '5498', '5510']
        modules = {'NondeterministicTime': 1, 'NondeterministicExponentialTime': 2}
        records = []
        for variant in variants:
            for module, scopes in modules.items():
                for negative in (False, True):
                    log = ''.join(self.scope_log([scope, scope + 2],
                                  [scope + (not negative), scope + 2 + (not negative)],
                                  scope, negative) for scope in range(1, scopes + 1))
                    records.append(dict(variant=variant, module=module, negative=negative,
                                        scopes=scopes, passed=scoped_control_passed(
                                            int(negative), log, scopes, negative)))
                    self.assertEqual(len(registration_counts(log)), scopes * 2)
        self.assertEqual(len(records), 16)
        self.assertEqual(sum(r['scopes'] for r in records), 24)
        self.assertTrue(attribute_matrix_complete(records, variants, modules))
        self.assertFalse(attribute_matrix_complete(records[:-1], variants, modules))
        self.assertFalse(attribute_matrix_complete(records + records[:1], variants, modules))
        self.assertFalse(attribute_matrix_complete(
            [dict(r, passed=False) if i == 15 else r for i, r in enumerate(records)],
            variants, modules))
        # A stale first-scope baseline cannot substitute for the second capture.
        stale = self.scope_log([1, 1], [2, 2]) + self.scope_log([1, 1], [4, 4], 2)
        self.assertFalse(scoped_control_passed(0, stale, 2))

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
