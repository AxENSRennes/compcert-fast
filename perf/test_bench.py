"""Reject false successes in differential execution before trusting timings."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import bench


class ExecutionChecks(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "expected").write_bytes(b"answer\n")
        self.case = {"args": [], "expected": "expected"}

    def execute(self, stdout=b"answer\n", stderr=b"COMPCERT_FAST_TIME 0.250000000\n", returncode=0):
        result = subprocess.CompletedProcess([], returncode, stdout, stderr)
        with patch.object(bench, "ROOT", self.root), patch.object(bench, "ARTIFACTS", self.root), \
                patch.object(bench.subprocess, "run", return_value=result):
            return bench.measure(self.root / "program", self.case)

    def test_correct_output_is_measured(self):
        self.assertEqual(self.execute(), 0.25)

    def test_wrong_output_is_rejected_even_with_valid_timing(self):
        with self.assertRaisesRegex(RuntimeError, "Incorrect stdout"):
            self.execute(stdout=b"wrong\n")

    def test_crash_is_rejected_even_with_correct_output(self):
        with self.assertRaisesRegex(RuntimeError, "exited -11"):
            self.execute(returncode=-11)

    def test_missing_clock_or_unexpected_diagnostics_are_rejected(self):
        for diagnostic in (b"", b"COMPCERT_FAST_TIME 0.250000000\nwarning\n"):
            with self.subTest(diagnostic=diagnostic), self.assertRaises(RuntimeError):
                self.execute(stderr=diagnostic)


if __name__ == "__main__":
    unittest.main()
