#!/usr/bin/env python3
"""Download only the Mathlib cache needed by the complete local source closure."""

from pathlib import Path
import subprocess

from consumers import imports


ROOT = Path(__file__).resolve().parents[1]


def main():
    bases = [ROOT, ROOT / "Vendor", ROOT / "Comparator"]
    bases += [p for p in (ROOT / ".lake/packages").iterdir() if p.is_dir()]
    pending = [path for folder in ["KVApproximation", "Vendor", "Comparator"]
               for path in (ROOT / folder).rglob("*.lean")]
    visited = set()
    mathlib = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        for module in imports(path.read_text()):
            if module == "Mathlib" or module.startswith("Mathlib."):
                mathlib.add(module)
                continue
            relative = Path(*module.split(".")).with_suffix(".lean")
            for base in bases:
                dependency = base / relative
                if dependency.is_file():
                    pending.append(dependency)
                    break
    if not mathlib:
        raise SystemExit("No Mathlib imports found; refusing an unscoped cache download.")
    print(f"Fetching the closure of {len(mathlib)} Mathlib imports", flush=True)
    subprocess.run(["lake", "exe", "cache", "get", *sorted(mathlib)], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
