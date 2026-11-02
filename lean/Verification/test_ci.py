#!/usr/bin/env python3
"""Checks for Comparator partitioning and complete-evidence validation."""

import json
import contextlib
import io
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

import collect_comparator as collector
import cache_dependencies
import resume_comparator
import verify
from verify import PARANOID_KERNELS, configurations, select_configurations


class ShardingTests(unittest.TestCase):
    def test_every_configuration_occurs_once(self):
        files, _ = configurations()
        shards = [select_configurations(files, i, 16) for i in range(16)]
        combined = [path for shard in shards for path in shard]
        self.assertEqual(sorted(combined), files)
        self.assertEqual(len(combined), len(set(combined)))
        self.assertLessEqual(max(map(len, shards)) - min(map(len, shards)), 1)

    def test_invalid_selections_are_rejected(self):
        files, _ = configurations()
        for index, count in [(-1, 16), (16, 16), (0, 0)]:
            with self.assertRaises(ValueError):
                select_configurations(files, index, count)
        with self.assertRaises(ValueError):
            select_configurations(files, selected=["does_not_exist"])
        with self.assertRaises(ValueError):
            select_configurations(files, 0, 16, [files[0].stem])


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config_path = self.root / "Comparator/example.json"
        self.config_path.parent.mkdir()
        self.config = {"theorem_names": ["example"], "challenge_module": "Challenge",
                       "solution_module": "Solution"}
        self.config_path.write_text(json.dumps(self.config))
        self.results = self.root / "results"
        self.results.mkdir()
        self.record_path = self.results / "comparator-example.json"
        self.record = {
            "command": ["lake", "comparator", "--config=Comparator/example.json", "--paranoid"],
            "configuration": "example.json", "exit_code": 0, "passed": True,
            "seconds": 1.0, "kernels_accepted": sorted(PARANOID_KERNELS), **self.config,
        }
        self.record_path.write_text(json.dumps(self.record))
        self.log = "\n".join(f"{k} kernel accepts the solution" for k in PARANOID_KERNELS)
        self.log += "\nYour solution is okay!\n"
        self.record_path.with_suffix(".log").write_text(self.log)
        self.root_patch = patch.object(collector, "ROOT", self.root)
        self.config_patch = patch.object(collector, "configurations",
                                         return_value=([self.config_path], {"example"}))
        self.root_patch.start()
        self.config_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.addCleanup(self.config_patch.stop)

    def test_complete_evidence_passes(self):
        self.assertTrue(collector.collect(self.results)["passed"])

    def test_missing_and_duplicate_results_fail(self):
        self.record_path.unlink()
        self.assertFalse(collector.collect(self.results)["passed"])
        self.record_path.write_text(json.dumps(self.record))
        extra = self.results / "duplicate"
        extra.mkdir()
        (extra / self.record_path.name).write_text(json.dumps(self.record))
        self.assertFalse(collector.collect(self.results)["passed"])

    def test_stale_or_weakened_evidence_fails(self):
        variants = [
            {"command": self.record["command"] + ["--inadvisably-no-sandbox"]},
            {"command": self.record["command"][:-1]},
            {"exit_code": 1},
            {"theorem_names": ["different_theorem"]},
            {"solution_module": "DifferentSolution"},
            {"kernels_accepted": ["Lean default"]},
        ]
        for change in variants:
            with self.subTest(change=change):
                self.record_path.write_text(json.dumps(self.record | change))
                self.assertFalse(collector.collect(self.results)["passed"])

    def test_missing_kernel_log_fails(self):
        self.record_path.with_suffix(".log").write_text("Your solution is okay!\n")
        self.assertFalse(collector.collect(self.results)["passed"])

    def test_resume_preserves_prior_success_when_next_check_fails(self):
        second = self.root / "Comparator/second.json"
        second.write_text(json.dumps(self.config | {"theorem_names": ["second"]}))
        original_record = self.record_path.read_bytes()
        original_log = self.record_path.with_suffix(".log").read_bytes()

        def fail_run(command, name):
            log = self.results / (name + ".log")
            log.write_text("The next check failed.\n")
            return {"command": command, "exit_code": 1, "seconds": 1.0}, log

        with patch.object(verify, "ROOT", self.root), \
             patch.object(verify, "RESULTS", self.results), \
             patch.object(verify.platform, "system", return_value="Linux"), \
             patch.object(verify, "configurations", return_value=([self.config_path, second], set())), \
             patch.object(verify, "run", side_effect=fail_run), \
             contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit):
                verify.comparator(selected=["second"], clear_existing=False)
        self.assertEqual(self.record_path.read_bytes(), original_record)
        self.assertEqual(self.record_path.with_suffix(".log").read_bytes(), original_log)
        failure = json.loads((self.results / "comparator-second.json").read_text())
        self.assertFalse(failure["passed"])

    def test_combining_ci_and_local_rejects_duplicate_results(self):
        local = self.root / "local"
        local.mkdir()
        (local / self.record_path.name).write_bytes(self.record_path.read_bytes())
        with self.assertRaisesRegex(ValueError, "Duplicate evidence"):
            resume_comparator.combine([self.results, local], self.root / "combined")

    def test_parallel_checks_preserve_separate_logs_and_prior_evidence(self):
        files = [self.config_path]
        for name in ["second", "third"]:
            path = self.root / "Comparator" / (name + ".json")
            path.write_text(json.dumps(self.config | {"theorem_names": [name]}))
            files.append(path)
        barrier = threading.Barrier(2, timeout=5)

        def succeed_run(command, name):
            barrier.wait()
            log = self.results / (name + ".log")
            log.write_text(name + "\n" + self.log)
            return {"command": command, "exit_code": 0, "seconds": 1.0}, log

        with patch.object(verify, "ROOT", self.root), \
             patch.object(verify, "RESULTS", self.results), \
             patch.object(verify.platform, "system", return_value="Linux"), \
             patch.object(verify, "configurations", return_value=(files, set())), \
             patch.object(collector, "configurations", return_value=(files, {"example", "second", "third"})), \
             patch.object(verify, "run", side_effect=succeed_run), \
             contextlib.redirect_stdout(io.StringIO()):
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(resume_comparator.run_one, name) for name in ["second", "third"]]
                self.assertTrue(all(future.result() for future in futures))
            self.assertTrue(collector.collect(self.results)["passed"])
        self.assertEqual(self.record_path.with_suffix(".log").read_text(), self.log)
        for name in ["second", "third"]:
            self.assertEqual((self.results / f"comparator-{name}.log").read_text(),
                             f"comparator-{name}\n" + self.log)
        self.assertFalse(list(self.results.glob("*.tmp")))


class CacheSelectionTests(unittest.TestCase):
    def test_transitive_external_imports_are_included_without_unrelated_modules(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            sources = {
                "KVApproximation/Example.lean": "module\npublic import LeanCert.Example\n",
                ".lake/packages/LeanCert/LeanCert/Example.lean":
                    "module\npublic import LeanCert.Helper\npublic import Mathlib.Required\n",
                ".lake/packages/LeanCert/LeanCert/Helper.lean": "import Mathlib.Transitive\n",
                ".lake/packages/LeanCert/LeanCert/Unused.lean": "import Mathlib\n",
            }
            for name, source in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            with patch.object(cache_dependencies, "ROOT", root), \
                 patch.object(cache_dependencies.subprocess, "run") as run, \
                 contextlib.redirect_stdout(io.StringIO()):
                cache_dependencies.main()
            self.assertEqual(run.call_args.args[0],
                             ["lake", "exe", "cache", "get", "Mathlib.Required", "Mathlib.Transitive"])


if __name__ == "__main__":
    unittest.main()
