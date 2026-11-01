#!/usr/bin/env python3
"""Checks for Comparator partitioning and complete-evidence validation."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import collect_comparator as collector
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


if __name__ == "__main__":
    unittest.main()
