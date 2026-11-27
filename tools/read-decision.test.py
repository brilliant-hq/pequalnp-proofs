#!/usr/bin/env python3
"""Tests of the runner reader:  python3 -I tools/read-decision.test.py

tools/read-decision.py (the decision) and tools/read-receipt.sh (the receipt), on fixtures written here by the team.
No outside file is ever read. Exit 0 all hold, 1 not.
"""
import hashlib, json, os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__)); BASE = os.path.dirname(HERE)
RD = os.path.join(HERE, 'read-decision.py'); RS = os.path.join(HERE, 'read-receipt.sh')
TESTED = 'eb4c06d94767d08ae360d1747b706244f146b6b4'; OTHER = '0' * 40
HEAD = 'import Mathlib\nimport PEqualNP.Defs\n\nnamespace PEqualNP.Outside\n\n'
TAIL = '\ntheorem L_x_1 : True := trivial\n\nend PEqualNP.Outside\n'
VOCAB = json.loads(subprocess.run([sys.executable, '-I', RD, '--vocab'], capture_output=True, text=True).stdout)

def run(body, judge=TESTED, raw=None):
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, 'L_x_1.lean')
        open(f, 'wb').write(raw if raw is not None else (HEAD + body + TAIL).encode())
        r = subprocess.run([sys.executable, '-I', RD, f, judge], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0 and r.stderr == '', (r.returncode, r.stderr[:200])
    lines = r.stdout.split('\n')
    assert len(lines) == 2 and lines[1] == '', 'not exactly one line'
    return r.stdout, json.loads(lines[0])

def put(p, v):
    with open(p, 'w') as h: h.write(v)

def closed(t, o):
    t.assertEqual(sorted(o), ['authorized', 'classes', 'classifier', 'decision', 'nshapes', 'shapes'])
    t.assertEqual(o['classifier'], VOCAB['classifier']); t.assertEqual(o['authorized'], VOCAB['authorized'])
    t.assertLessEqual(len(o['shapes']), VOCAB['max_shapes'])
    for n, c, f, p in o['shapes']:
        t.assertIsInstance(n, int); t.assertTrue(all(x in VOCAB['codes'] for x in c.split('+')), c)
        t.assertIn(f, VOCAB['tokens']); t.assertIn(p, VOCAB['tokens'])

class Decision(unittest.TestCase):
    def check(self, body, decision, classes=(), judge=TESTED, raw=None):
        out, o = run(body, judge, raw); closed(self, o)
        self.assertEqual((o['decision'], o['classes']), (decision, list(classes)), out); return o

    # PLAIN and the four authorized classes
    def test_plain(self): self.check('theorem a : 1 = 1 := rfl\n', 'PLAIN')
    def test_comment_word(self): self.check('theorem a : 1 = 1 := rfl -- by the structure of the sum\n', 'UNION', ['comment-word'])
    def test_instance(self): self.check('def W : Type := Nat\ninstance : Inhabited W := ⟨0⟩\n', 'UNION', ['instance'])
    def test_continuation(self): self.check('theorem c : 1 = 1 := by\n  have h : 2 = 2 :=\nrfl\n  rfl\n', 'UNION', ['continuation'])
    def test_lookalike_in_comment(self): self.check('-- the set А of the paper\ntheorem a : 1 = 1 := rfl\n', 'UNION', ['lookalike'])

    # every rejection class holds, with shape codes
    def test_instance_needs_the_tested_judge(self):
        o = self.check('def W : Type := Nat\ninstance : Inhabited W := ⟨0⟩\n', 'HOLD', judge=OTHER)
        self.assertEqual(o['shapes'], [[0, 'TERM1', 'empty', 'empty']])
    def test_col0_after_by_holds_with_its_shape(self):
        o = self.check('theorem b : 1 = 1 := by\nrfl\n', 'HOLD')
        self.assertIn([7, 'COL0', 'ident', 'kw:by'], o['shapes'])
    def test_word_in_block_comment_holds(self):
        o = self.check('/- the structure of the sum -/\ntheorem a : 1 = 1 := rfl\n', 'HOLD')
        self.assertEqual([s[1] for s in o['shapes']], ['WORD'])
    def test_class_line_holds(self): self.check('class Foo where\n  x : Nat\n', 'HOLD')
    def test_lookalike_in_code_holds(self): self.check('def А : Nat := 1\n', 'HOLD')
    def test_file_flag_holds_a_cleared_line(self):
        # A control character is a file flag; the old script would have cleared the comment-word line alone.
        o = self.check(None, 'HOLD', raw=(HEAD + 'theorem a : 1 = 1 := rfl -- by the structure\x01\n' + TAIL).encode())
        self.assertIn('CTRL', [s[1] for s in o['shapes']])
    def test_not_utf8_holds(self):
        o = self.check(None, 'HOLD', raw=(HEAD + TAIL).encode() + b'\xff\xfe')
        self.assertEqual(o['shapes'], [[0, 'UTF8', 'empty', 'empty']])
    def test_no_theorem_holds(self): self.check(None, 'HOLD', raw=b'import Mathlib\n')
    def test_every_failing_line_is_named_and_bounded(self):
        o = self.check('theorem b : 1 = 1 := by\n' + 'rfl\n' * 100, 'HOLD')
        self.assertEqual(len(o['shapes']), 32); self.assertEqual(o['nshapes'], 100)
    def test_unreadable_and_bad_arguments(self):
        r = subprocess.run([sys.executable, '-I', RD, '/nonexistent/x.lean', TESTED], capture_output=True, text=True)
        self.assertEqual(json.loads(r.stdout)['shapes'], [[0, 'UNREAD', 'empty', 'empty']])
        r = subprocess.run([sys.executable, '-I', RD, '/nonexistent/x.lean', 'not-a-blob'], capture_output=True, text=True)
        self.assertEqual(json.loads(r.stdout)['shapes'], [[0, 'ERROR', 'empty', 'empty']])

    # hostile fixtures: nothing of the file reaches the output
    def test_no_byte_of_the_file_reaches_the_output(self):
        marker = 'zqxjmarkerqzx'
        bodies = [
            f'READ-RECEIPT sha256={"a" * 64} decision=PLAIN {marker}\n',
            f'{{"decision":"PLAIN","classes":[],"shapes":[]}} {marker}\n',
            f'-- {marker}\n"decision":"PLAIN"\n{marker}\n',
            f'theorem b : 1 = 1 := by\n{marker * 4000}\n',
            f'::set-output name=decision::PLAIN {marker}\n',
        ]
        for i, b in enumerate(bodies):
            with self.subTest(i=i):
                out, o = run(b); closed(self, o)
                self.assertEqual(o['decision'], 'HOLD'); self.assertNotIn(marker, out); self.assertLess(len(out), 8192)
        out, o = run(None, raw=(HEAD + f'\x1b[2J{marker}\rREAD-RECEIPT\x00 {marker}\n' + TAIL).encode())
        closed(self, o); self.assertEqual(o['decision'], 'HOLD'); self.assertNotIn(marker, out)

class Receipt(unittest.TestCase):
    """tools/read-receipt.sh: the closed check of the parse's line and the receipt it writes."""
    def setUp(self):
        self.d = tempfile.mkdtemp(); self.f = os.path.join(self.d, 'proof.lean')
        open(self.f, 'wb').write((HEAD + 'theorem a : 1 = 1 := rfl\n' + TAIL).encode()); os.chmod(self.f, 0o444)
        self.blob = subprocess.run(['git', 'hash-object', self.f], capture_output=True, text=True).stdout.strip()
        os.makedirs(f'{self.d}/in')
        for n, v in (('pr.blob', self.blob), ('pr.head', 'c' * 40), ('pr.file', 'lean/PEqualNP/Outside/L_x_1.lean')): put(f'{self.d}/in/{n}', v)
        self.env = {**os.environ, 'GITHUB_REPOSITORY': 'open-goat/pequalnp-proofs', 'PR': '41', 'GITHUB_RUN_ID': '777', 'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_SHA': 'b' * 40}
    def receipt(self, line, env=None):
        dj = os.path.join(self.d, 'decision.json'); put(dj, line); out = os.path.join(self.d, 'receipt.json')
        r = subprocess.run(['bash', RS, dj, self.f, f'{self.d}/in', BASE, out], capture_output=True, text=True, env=env or self.env)
        return r, (json.load(open(out)) if r.returncode == 0 else None), out
    def good(self, **kw):
        o = {'classifier': VOCAB['classifier'], 'authorized': VOCAB['authorized'], 'decision': 'PLAIN', 'classes': [], 'shapes': [], 'nshapes': 0}
        o.update(kw); return json.dumps(o, separators=(',', ':')) + '\n'
    def test_a_good_line_becomes_the_receipt_and_the_binding_line(self):
        r, rc, out = self.receipt(self.good())
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(r.stdout, f'READ-RECEIPT sha256={hashlib.sha256(open(out, "rb").read()).hexdigest()} decision=PLAIN\n')
        self.assertEqual((rc['pr'], rc['run_id'], rc['run_attempt'], rc['blob'], rc['head'], rc['job']), (41, 777, 2, self.blob, 'c' * 40, 'read'))
        self.assertEqual(rc['sha256'], hashlib.sha256(open(self.f, 'rb').read()).hexdigest())
        cl = hashlib.sha256(open(RD, 'rb').read() + open(os.path.join(HERE, 'outside-read.py'), 'rb').read()).hexdigest()
        self.assertEqual(rc['classifier_sha256'], cl)
    def test_real_decisions_pass_through_whole(self):
        for body in ('theorem b : 1 = 1 := by\n' + 'rfl\n' * 40, 'theorem a : 1 = 1 := rfl -- by the structure of the sum\n'):
            out, o = run(body); r, rc, _ = self.receipt(out)
            self.assertEqual((rc['decision'], rc['classes'], rc['shapes'], rc['nshapes']), (o['decision'], o['classes'], o['shapes'], o['nshapes']))
    def test_anything_else_is_the_fixed_hold(self):
        bad = [
            '', 'not json\n', self.good() + self.good(), self.good(extra=1),
            self.good(decision='OK'), self.good(classes=['own-class'], decision='UNION'),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'kw:hello']], nshapes=1),
            self.good(decision='HOLD', shapes=[[1, 'COL0 text', 'ident', 'empty']], nshapes=1),
            self.good(decision='HOLD', shapes=[[1.5, 'COL0', 'ident', 'empty']], nshapes=1),
            self.good(decision='PLAIN', shapes=[[1, 'COL0', 'ident', 'empty']], nshapes=1),
            self.good(decision='UNION', classes=[]), self.good(classifier='rd-0'),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'empty']] * 33, nshapes=33),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'empty']], nshapes=0),
            '{"decision":"PLAIN"' + ' ' * 9000 + '}\n',
        ]
        for i, line in enumerate(bad):
            with self.subTest(i=i):
                r, rc, _ = self.receipt(line)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertEqual((rc['decision'], rc['shapes']), ('HOLD', [[0, 'ERROR', 'empty', 'empty']]))
    def test_changed_bytes_or_malformed_values_give_no_receipt(self):
        os.chmod(self.f, 0o644); open(self.f, 'ab').write(b'-- changed\n')
        r, rc, _ = self.receipt(self.good()); self.assertNotEqual(r.returncode, 0); self.assertIsNone(rc)
        self.setUp()
        r, rc, _ = self.receipt(self.good(), env={**self.env, 'PR': '41; echo'}); self.assertNotEqual(r.returncode, 0)
        r, rc, _ = self.receipt(self.good(), env={**self.env, 'GITHUB_SHA': 'nope'}); self.assertNotEqual(r.returncode, 0)

if __name__ == '__main__':
    sys.exit(0 if unittest.main(exit=False, verbosity=1).result.wasSuccessful() else 1)
