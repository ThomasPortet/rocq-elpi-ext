#!/usr/bin/env python3
import argparse
import csv
import re
import shlex
import shutil
import subprocess
import time
from pathlib import Path
from collections import defaultdict
from statistics import mean, stdev


def make_test(n, prelude):
    return f"""
From elpi.ext Require Import automation.
From Stdlib Require Import Reals Lra.


Lemma test{n} x (p : x +1 <>0) :
  r {n} x = r_alt {n} x.
Proof.
  unfold r, r_alt.
  Time deep_field.
  reflexivity.
  all:nra.
Qed.
"""


def find_compiler(command=None):
    if command:
        return shlex.split(command)

    if shutil.which("rocq"):
        return [
            "rocq", "compile",
            "-R", "../../stdlib/theories", "Stdlib",
            "-I", "../_build/install/default/lib",
            "-Q", "../_build/default/tests", "ext.tests",
            "-R",
            "/home/tportet/these/rocq-elpi-ext/_build/default/theories",
            "elpi.ext",
        ]

    raise RuntimeError("Install Rocq or pass --compiler.")


def extract_time(output):
    patterns = [
        r"Finished transaction in\s+([0-9]+(?:\.[0-9]+)?)\s+secs?",
        r"Finished transaction in\s+([0-9]+(?:\.[0-9]+)?)\s+seconds?",
    ]

    for pattern in patterns:
        matches = re.findall(pattern, output)
        if matches:
            return float(matches[-1])

    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("prelude", help="File containing imports and definitions")
    parser.add_argument("--start", type=int, default=1)
    parser.add_argument("--end", type=int, default=30)
    parser.add_argument("--step", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--compiler", default=None)
    parser.add_argument("--out", default="deep_field_bench")
    parser.add_argument("--batches", type=int, default=1)
    args = parser.parse_args()

    prelude_path = Path(args.prelude).resolve()
    prelude = prelude_path.read_text(encoding="utf-8")
    out = Path(args.out).resolve()
    cases = out / "cases"
    cases.mkdir(parents=True, exist_ok=True)

    compiler = find_compiler(args.compiler)
    rows = []

    for batch in range(1, args.batches + 1):
        print(f"\n=== Batch {batch}/{args.batches} ===")

        for n in range(args.start, args.end + 1, args.step):
            source = cases / f"test{n}.v"
            source.write_text(make_test(n, prelude), encoding="utf-8")

            command = compiler + [str(source)]
            started = time.perf_counter()

            try:
                print(shutil.which("rocq"))
                print("CWD:", prelude_path.parent)
                print("COMMAND:", shlex.join(command))

                proc = subprocess.run(
                    command,
                    cwd=prelude_path.parent,
                    capture_output=True,
                    text=True,
                    timeout=args.timeout,
                )

                wall = time.perf_counter() - started
                output = proc.stdout + "\n" + proc.stderr
                tactic_time = extract_time(output)

                if proc.returncode != 0:
                    status = "failed"
                elif tactic_time is None:
                    status = "time_not_found"
                else:
                    status = "ok"

            except subprocess.TimeoutExpired:
                wall = time.perf_counter() - started
                output = ""
                tactic_time = None
                status = "timeout"

            (cases / f"test{n}_batch{batch}.log").write_text(
                f"Command: {shlex.join(command)}\n"
                f"Status: {status}\n\n{output}",
                encoding="utf-8",
            )

            rows.append({
                "batch": batch,
                "n": n,
                "tactic_seconds": tactic_time,
                "wall_seconds": round(wall, 6),
                "status": status,
            })

            print(
                f"batch={batch:2} | n={n:4} | {status:16} | "
                f"deep_field="
                f"{tactic_time if tactic_time is not None else 'N/A'}"
            )

    csv_path = out / "results.csv"

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "batch", "n", "tactic_seconds", "wall_seconds", "status"
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    # Aggregate successful runs by n.
    grouped = defaultdict(list)

    for row in rows:
        if row["status"] == "ok":
            grouped[row["n"]].append(row)

    summary_rows = []

    for n in range(args.start, args.end + 1, args.step):
        successful = grouped[n]
        times = [r["tactic_seconds"] for r in successful]
        wall_times = [r["wall_seconds"] for r in successful]

        summary_rows.append({
            "n": n,
            "successful_runs": len(successful),
            "total_runs": args.batches,
            "tactic_mean": mean(times) if times else None,
            "tactic_std": stdev(times) if len(times) > 1 else None,
            "wall_mean": mean(wall_times) if wall_times else None,
            "wall_std": stdev(wall_times) if len(wall_times) > 1 else None,
        })

    summary_path = out / "summary.csv"

    with summary_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "n", "successful_runs", "total_runs",
                "tactic_mean", "tactic_std",
                "wall_mean", "wall_std",
            ],
        )
        writer.writeheader()
        writer.writerows(summary_rows)

    for row in summary_rows:
        print(
            f"n={row['n']:4} | "
            f"{row['successful_runs']}/{row['total_runs']} successful | "
            f"mean={row['tactic_mean']} s | "
            f"std={row['tactic_std']} s"
        )

    print(f"Summary saved to {summary_path}")

    # Plot mean tactic time for each n.
    plotted = [
        row for row in summary_rows
        if row["tactic_mean"] is not None
    ]

    if plotted:
        try:
            import matplotlib.pyplot as plt

            x = [row["n"] for row in plotted]
            y = [row["tactic_mean"] for row in plotted]

            plt.figure()
            plt.plot(x, y, marker="o")
            plt.xlabel("n")
            plt.ylabel("Mean tactic time (s)")
            plt.title("deep_field benchmark")
            plt.grid(True)
            plt.tight_layout()
            plt.savefig(out / "results.png", dpi=160)
            plt.close()

            print(f"Plot saved to {out / 'results.png'}")

        except ImportError:
            print("Install matplotlib to generate the plot.")

    print(f"CSV saved to {csv_path}")
    print(f"Generated tests and logs saved to {cases}")


if __name__ == "__main__":
    main()
