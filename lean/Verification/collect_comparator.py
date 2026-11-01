#!/usr/bin/env python3
"""Require one successful sandboxed paranoid result for every configuration."""

import argparse
from collections import Counter
import json
from pathlib import Path

from verify import PARANOID_KERNELS, ROOT, configurations


def collect(results_dir):
    files, theorems = configurations()
    expected = {"comparator-" + path.stem + ".json": path for path in files}
    records = list(results_dir.rglob("comparator-*.json"))
    counts = Counter(path.name for path in records)
    missing = sorted(set(expected) - set(counts))
    unexpected = sorted(set(counts) - set(expected))
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    invalid = []
    seconds = 0.0
    for path in records:
        if path.name not in expected:
            continue
        config_path = expected[path.name]
        config = json.loads(config_path.read_text())
        try:
            record = json.loads(path.read_text())
            log = path.with_suffix(".log").read_text()
            command = ["lake", "comparator", "--config=" + str(config_path.relative_to(ROOT)),
                       "--paranoid"]
            valid = (record.get("passed") is True and record.get("exit_code") == 0
                     and record.get("command") == command
                     and record.get("configuration") == config_path.name
                     and record.get("theorem_names") == config["theorem_names"]
                     and record.get("challenge_module") == config["challenge_module"]
                     and record.get("solution_module") == config["solution_module"]
                     and set(record.get("kernels_accepted", [])) == PARANOID_KERNELS
                     and "Your solution is okay!" in log
                     and all(f"{kernel} kernel accepts the solution" in log
                             for kernel in PARANOID_KERNELS))
            seconds += float(record.get("seconds", 0))
        except (OSError, ValueError, TypeError, AttributeError):
            valid = False
        if not valid:
            invalid.append(path.name)
    return {
        "configurations_expected": len(expected),
        "configurations_received": len(records),
        "theorems_expected": len(theorems),
        "required_kernels": sorted(PARANOID_KERNELS),
        "missing": missing,
        "unexpected": unexpected,
        "duplicates": duplicates,
        "failed_or_invalid": sorted(invalid),
        "configuration_seconds": round(seconds, 1),
        "passed": not (missing or unexpected or duplicates or invalid),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results_dir", type=Path)
    args = parser.parse_args()
    summary = collect(args.results_dir)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    (args.results_dir / "coverage.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    raise SystemExit(0 if summary["passed"] else 1)
