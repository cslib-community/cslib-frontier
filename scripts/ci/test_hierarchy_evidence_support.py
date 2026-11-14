import subprocess
import tempfile
from pathlib import Path
import unittest
from hierarchy_evidence_support import BASELINE, HELPER, PROBE, LOCAL, attribute_control_passed, instrument, restore_snapshot, scoped_control_passed, attribute_matrix_complete, registration_counts


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
        self.assertNotIn('initialize', positive)
        self.assertNotIn('IO.Ref', positive)
        self.assertIn('private meta def hierarchyEvidence5530Counts', positive)
        self.assertEqual(positive.replace(LOCAL, ''), negative)
        self.assertEqual(positive.count('Lean.Elab.Command.modifyScope'), 2)
        self.assertIn('COUNTS 1 baseline', positive)
        self.assertIn('COUNTS 2 baseline', positive)
        self.assertIn('COUNTS 2 inside', positive)
        self.assertEqual(positive.count('(ts.filter (· == t)).size'), 2)

    def test_original_clients_roundtrip_and_scope_options(self):
        # Actual clients cover both independent NEXP sites at every measured revision.
        root = Path(__file__).resolve().parents[2]
        revisions = ('39b11c9de', '55c7e0dabb4fab4ecf9deb9373d502ba4dfb231f',
                     'b50dee8e88b6b0d6154654d2e30e918d3a1acefd',
                     '28c3dffb82a3102754689396c2b7609036ba60aa')
        prefix = 'CslibFrontier/Computability/Complexity/Classes/Hierarchy/'
        for revision in revisions:
            for module, scopes in (('NondeterministicTime', 1),
                                   ('NondeterministicExponentialTime', 2)):
                with self.subTest(revision=revision, module=module):
                    source = subprocess.check_output(
                        ['git', 'show', f'{revision}:{prefix}{module}.lean'],
                        cwd=root, text=True)
                    positive, count = instrument(source)
                    negative, neg_count = instrument(source, negative=True)
                    self.assertEqual((count, neg_count), (scopes, scopes))
                    self.assertEqual(positive.replace(LOCAL, ''), negative)
                    self.assertNotIn('initialize', positive)
                    self.assertNotIn('IO.Ref', positive)
                    self.assertNotIn('registerEnvExtension', positive)
                    self.assertEqual(positive.count(HELPER), 1)
                    restored = positive.replace(HELPER, '', 1)
                    for scope in range(1, scopes + 1):
                        capture = BASELINE.replace('{scope}', str(scope))
                        probe = PROBE.replace('{scope}', str(scope))
                        self.assertEqual(restored.count(capture), 1)
                        self.assertEqual(restored.count(probe), 1)
                        self.assertLess(restored.index(capture), restored.index(probe))
                        for field, index in (('fst', 0), ('snd', 1)):
                            key = f'`hierarchyEvidence5530.baseline{scope}.{field}'
                            self.assertIn(f'{key} counts[{index}]!', capture)
                            self.assertIn(f'opts.get? (α := Nat) {key}', probe)
                            self.assertEqual(positive.count(key), 2)
                        # The write must affect Command state after the lifted count
                        # returns; a withOptions around only that count cannot persist.
                        self.assertIn('run_cmd do\n  let counts ← Lean.Elab.Command.liftTermElabM', capture)
                        self.assertIn('Lean.Elab.Command.modifyScope fun scope => { scope with\n    opts := (scope.opts.set', capture)
                        self.assertIn('let opts ← Lean.getOptions', probe)
                        self.assertEqual(probe.count('HIERARCHY_ATTRIBUTE_BASELINE_MISSING'), 2)
                        self.assertIn('counts == baseline.map (· + 1)', probe)
                        restored = restored.replace(capture, '', 1).replace(probe, '', 1)
                    self.assertEqual(restored, source)

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
