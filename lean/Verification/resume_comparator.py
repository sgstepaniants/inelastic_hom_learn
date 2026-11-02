#!/usr/bin/env python3
"""Finish missing sandboxed checks, preserving each completed local result."""

import fcntl
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import platform
import resource
import shutil

from collect_comparator import collect
import verify


PILOT = ("dirichlet_compactness", "dirichlet_weak_compactness", "homogenized_green")


def run_one(name):
    try:
        verify.comparator(selected=[name], clear_existing=False)
    except SystemExit:
        return False
    return True


def parallel_jobs(requested):
    if requested is not None:
        return requested
    memory = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    available_kib = int(memory["MemAvailable"].split()[0])
    measured_kib = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    peak_kib = max(measured_kib, 3 * 1024**2)
    jobs = 2 if (os.cpu_count() or 1) >= 4 and available_kib >= 2 * peak_kib + 512 * 1024 else 1
    print(f"Pilot peak child RSS: {measured_kib / 1024:.0f} MiB; "
          f"reserving {peak_kib / 1024:.0f} MiB per check; "
          f"available: {available_kib / 1024:.0f} MiB; parallel checks: {jobs}", flush=True)
    return jobs


def combine(sources, destination):
    destination.mkdir(parents=True, exist_ok=True)
    for path in destination.glob("comparator-*"):
        if path.is_file():
            path.unlink()
    for source in sources:
        for record in sorted(source.glob("comparator-*.json")):
            target = destination / record.name
            if target.exists():
                raise ValueError(f"Duplicate evidence: {record.name}")
            shutil.copyfile(record, target)
            log = record.with_suffix(".log")
            if log.exists():
                shutil.copyfile(log, target.with_suffix(".log"))
    summary = collect(destination)
    (destination / "coverage.json").write_text(json.dumps(summary, indent=2) + "\n")
    if summary["unexpected"] or summary["duplicates"]:
        raise ValueError("Unexpected or duplicate Comparator results")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, choices=[1, 2],
                        help="Concurrent checks after the serial pilot; default uses its memory measurement")
    args = parser.parse_args()
    if platform.system() != "Linux":
        raise SystemExit("Run this recovery inside the Linux proof VM.")
    results = verify.ROOT / "Verification/results"
    saved = results / "ci"
    local = results / "local"
    combined = results / "combined"
    local.mkdir(parents=True, exist_ok=True)
    lock_path = verify.ROOT / ".work/local-comparator.lock"
    lock_path.parent.mkdir(exist_ok=True)
    with lock_path.open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("A local Comparator recovery is already running.")
        baseline = collect(saved)
        if baseline["failed_or_invalid"] or baseline["unexpected"] or baseline["duplicates"]:
            raise SystemExit("Preserved CI evidence is invalid; refusing to reuse it.")
        summary = combine([saved, local], combined)
        pending = {
            Path(name).stem.removeprefix("comparator-")
            for name in summary["missing"] + summary["failed_or_invalid"]
        }
        pilot = [name for name in PILOT if name in pending]
        remaining = sorted(pending - set(PILOT))
        print(f"Preserving {summary['configurations_received'] - len(summary['failed_or_invalid'])} "
              f"successful checks; {len(pending)} remain", flush=True)
        verify.RESULTS = local

        def checkpoint():
            result = combine([saved, local], combined)
            valid = result["configurations_received"] - len(result["failed_or_invalid"])
            print(f"Validated {valid}/{result['configurations_expected']} configurations", flush=True)
            return result

        for name in pilot:
            print(f"Repaired pilot: {name}", flush=True)
            passed = run_one(name)
            summary = checkpoint()
            if not passed:
                raise SystemExit(f"Repaired pilot failed: {name}; completed evidence preserved.")
        if remaining:
            pool = ThreadPoolExecutor(max_workers=parallel_jobs(args.jobs))
            try:
                futures = {pool.submit(run_one, name): name for name in remaining}
                for future in as_completed(futures):
                    future.result()
                    summary = checkpoint()
            finally:
                pool.shutdown(wait=True, cancel_futures=True)
        if not summary["passed"]:
            raise SystemExit("Comparator coverage is incomplete; resume after resolving failures.")
        print("All configurations passed sandboxed Comparator and all six kernels.", flush=True)


if __name__ == "__main__":
    main()
