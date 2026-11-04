"""Regression tests against weakened manifests, assumptions and stale success."""
import json
import os
import shutil
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import guard
import integrity
import proofs


class SourceGateTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.original = {
            "LICENSE": b"unchanged license\n",
            "driver/Compiler.v": b"Theorem correct: True. Proof. exact I. Qed.\n",
            "aarch64/Asm.v": b"Definition semantics := True.\n",
            "backend/Linearize.v": b"Parameter oracle: nat.\nDefinition enum := oracle.\n",
            "backend/Linearizeproof.v": b"Lemma complete: True. Proof. exact I. Qed.\n",
            "extraction/extraction.v": b"Require Import Extraction.\n",
            "Makefile": b"check-proof:\n\tcoqchk Compiler\n",
        }
        for name, data in self.original.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (self.root / "perf").mkdir()
        self.lock = {"upstream_commit": integrity.UPSTREAM,
                     "files": {name: integrity.sha(data) for name, data in self.original.items()
                               if name.endswith((".v", ".vp")) or name == "LICENSE"}}
        self.write("trust-lock.json", self.lock)
        self.write("proved-changes.json", {})

    def write(self, name, value):
        (self.root / "perf" / name).write_text(json.dumps(value))

    def check(self):
        tracked = "\0".join(self.original).encode()
        with patch.object(guard, "ROOT", self.root), \
                patch.object(guard, "upstream_sources", return_value=self.original), \
                patch.object(guard.subprocess, "check_output", return_value=tracked):
            guard.main()

    def test_original_passes(self):
        self.check()

    def test_edited_original_manifest_cannot_authorize_weakened_theorem(self):
        name = "driver/Compiler.v"
        (self.root / name).write_text("Axiom correct: False.\n")
        self.lock["files"][name] = integrity.sha((self.root / name).read_bytes())
        self.write("trust-lock.json", self.lock)
        with self.assertRaisesRegex(SystemExit, "fixed upstream"):
            self.check()

    def test_review_manifest_cannot_authorize_main_theorem_change(self):
        self.write("proved-changes.json", {"driver/Compiler.v": "arbitrary"})
        with self.assertRaisesRegex(SystemExit, "Unapproved"):
            self.check()

    def test_build_recipe_cannot_replace_kernel_check_with_echo(self):
        (self.root / "Makefile").write_text("check-proof:\n\techo success\n")
        with self.assertRaisesRegex(SystemExit, "Makefile"):
            self.check()

    def test_reviewed_proof_cannot_add_an_axiom_or_change_an_existing_statement(self):
        name = "backend/Linearizeproof.v"
        for source in ("Axiom shortcut: False.\n" + self.original[name].decode(),
                       "Lemma complete: False. Proof. exact I. Qed.\n",
                       self.original[name].decode() + "Unset Guard Checking.\n",
                       self.original[name].decode() + "Declare Module Hidden.\n"):
            with self.subTest(source=source):
                (self.root / name).write_text(source)
                self.write("proved-changes.json", {name: integrity.sha(source.encode())})
                with self.assertRaisesRegex(SystemExit, "unchecked commands"):
                    self.check()


class AssumptionsTests(unittest.TestCase):
    def test_comments_and_strings_do_not_create_fake_admissions(self):
        source = '(* outer (* Axiom bad: False. *) *) Definition text := "Admitted.".\n'
        self.assertEqual(integrity.assumption_commands(source), {})

    def test_unchecked_cast_is_detected_inside_a_proof(self):
        self.assertNotEqual(integrity.assumption_commands("exact_no_check I."), {})

    def test_principal_assumptions_ignore_order_but_not_changed_types(self):
        original = "Axioms:\nfoo : nat\nbar : True\nAxioms:\nfoo : nat\nbar : True\n"
        reordered = "Axioms:\nbar : True\nfoo : nat\nAxioms:\nbar : True\nfoo : nat\n"
        self.assertEqual(integrity.canonical_assumptions(original), integrity.canonical_assumptions(reordered))
        self.assertNotEqual(integrity.canonical_assumptions(original),
                            integrity.canonical_assumptions(reordered.replace("foo : nat", "foo : bool")))

    def test_failed_verification_invalidates_previous_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "perf/results/proofs.json"
            output.parent.mkdir(parents=True)
            output.write_text('{"success": true}\n')
            previous_cwd = Path.cwd()
            try:
                with patch.object(proofs, "ROOT", root), \
                        patch.object(proofs, "run", side_effect=RuntimeError("guard refuses")):
                    with self.assertRaisesRegex(RuntimeError, "guard refuses"):
                        proofs.verify(1)
            finally:
                os.chdir(previous_cwd)
            actual = json.loads(output.read_text())
            self.assertFalse(actual["success"])
            self.assertEqual(actual["stage"], "source gate")
            self.assertIn("guard refuses", actual["error"])

    def test_public_make_entry_invalidates_success_when_the_guard_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "perf/results").mkdir(parents=True)
            output = root / "perf/results/proofs.json"
            output.write_text('{"success": true}\n')
            for name in ("Makefile.fast", "perf/proofs.py", "perf/integrity.py"):
                shutil.copy2(proofs.ROOT / name, root / name)
            (root / "perf/guard.py").write_text("raise SystemExit('refuse changed semantics')\n")
            wrapper = root / "perf/in-env"
            wrapper.write_text('#!/bin/sh\nexec "$@"\n')
            wrapper.chmod(0o755)
            result = subprocess.run(["make", "-f", "Makefile.fast", "proofs"],
                                    cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(output.read_text())
            self.assertFalse(report["success"])
            self.assertEqual(report["stage"], "source gate")


if __name__ == "__main__":
    unittest.main()
