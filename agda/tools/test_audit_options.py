#!/usr/bin/env python3
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.dont_write_bytecode = True
import audit_options as a

class LexerTests(unittest.TestCase):
    def test_comments_strings_and_evidence(self):
        text = ('{- outer {- inner -} {-# TERMINATING #-} postulate ? -}\n'
                '-- {-# NON_TERMINATING #-}\n'
                's = "postulate ? {-# REWRITE x #-} \\""\n'
                '{-# OPTIONS --allow-unsolved-metas #-}\n'
                '{-# TERMINATING #-}\npostulate A : Set\nx = ?\ny = {! postulate ? !}\n')
        result = a.scan(text, '/fixture.agda')
        self.assertEqual([x['line'] for x in result['findings']], [4, 5, 6, 7, 8])
        self.assertEqual(len(result['pragmas']), 2)
        self.assertTrue(all(x['path'] == '/fixture.agda' for x in result['findings']))
        self.assertEqual(result['findings'][0]['evidence'], text.splitlines()[3])

    def test_every_forbidden_and_benign_option(self):
        text = '{-# OPTIONS ' + ' '.join(sorted(a.UNSAFE | a.BENIGN)) + ' #-}\n'
        text += '\n'.join('{-# ' + name + ' f #-}' for name in a.FORBIDDEN)
        result = a.scan(text, 'fixture')
        self.assertEqual(len(result['findings']), len(a.UNSAFE) + len(a.FORBIDDEN))
        self.assertEqual(len(result['benign_options']), len(a.BENIGN))
        self.assertFalse(a.scan('postulate-name = "?"\np? = \'?\'', 'fixture')['findings'])
        self.assertEqual(len(a.scan('flags:--type-in-type\n', 'lib', True)['findings']), 1)


class GraphTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.p = Path(tmp.name)
        env = patch.dict(os.environ, {'CUBICAL_DIR': ''})
        env.start()
        self.addCleanup(env.stop)
        def write(name, text):
            path = self.p / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.write = write
        for root in a.ROOTS:
            write('src/' + root.replace('.', '/') + '.agda',
                  f'module {root} where\nopen import Cubical.Base\nopen import Agda.Primitive\n')
        write('roots.txt', '\n'.join(sorted(a.ROOTS)))
        write('src/DeloopS3/Unused.agda', 'module DeloopS3.Unused where\npostulate Bad : Set\n')
        write('vendor/Cubical/Base.agda', 'module Cubical.Base where\n{-# OPTIONS --lossy-unification #-}\n')
        flags = sorted(a.BENIGN)
        for lib in ('local.agda-lib', 'vendor/cubical.agda-lib'):
            write(lib, 'flags: ' + ' '.join(flags) + '\n')
        write('deps.lock.json', json.dumps({'project': {'library_file': 'local.agda-lib', 'flags': flags},
                                          'cubical': {'path': 'vendor', 'flags': flags}}))

    def test_exact_closure_benign_and_library_lock(self):
        report = a.audit(self.p)
        self.assertTrue(report['ok'], report['errors'])
        self.assertEqual(report['counts']['sources'], 3)
        self.assertEqual(report['counts']['benign_options'], 9)
        self.assertEqual(report['excluded_compiler_builtins'], ['Agda.Primitive'])
        self.write('vendor/cubical.agda-lib', 'flags: --allow-unsolved-metas\n')
        report = a.audit(self.p)
        self.assertFalse(report['ok'])
        self.assertEqual(report['findings'][0]['token'], '--allow-unsolved-metas')
        self.assertTrue(report['errors'])

    def test_missing_graph_and_vendor_findings(self):
        self.write('vendor/Cubical/Base.agda', 'module Cubical.Base where\npostulate Bad : Set\n')
        self.assertEqual(a.audit(self.p)['counts']['findings'], 1)
        (self.p / 'vendor/Cubical/Base.agda').unlink()
        self.assertFalse(a.audit(self.p)['ok'])


if __name__ == '__main__':
    unittest.main()
