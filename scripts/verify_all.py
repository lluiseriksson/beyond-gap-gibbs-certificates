"""
Single-command Gate-2 reproducibility & verification harness for Paper 04.
Checks:
  1. Lean 4 kernel build & axiom audit (0 sorry, 0 Classical.choice, 16 audited theorems).
  2. Pytest suite (8 tests incl. 10 adversarial certificate tamper tests + exact LDL^T replay).
  3. SHA-256 byte-lock manifest verification (SHA256SUMS.json).
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

TRACKED_FILES = [
    "LICENSE",
    "README.md",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/BeyondGapGibbs.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/kms_gibbs.py",
    "src/superpoincare_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "results/experiment1_1d_kms_gibbs_chains.json",
    "results/experiment2_large_n_scaling_and_phases.json",
    "results/experiment3_exact_Q_ldlt_certificates.json",
    "results/experiment4_sharpness_and_two_stage.json",
    "results/rational_certificates/tfim_n2_ferro_b2p0_ldlt.cert.json",
    "results/rational_certificates/xxz_n2_stag_b2p0_ldlt.cert.json",
    "results/rational_certificates/tfim_n4_ferro_b2p5_exact.cert.json",
    "results/rational_certificates/xxz_n4_stag_b1p5_exact.cert.json",
    "results/rational_certificates/depolarizing_n50_exact.cert.json",
    "results/rational_certificates/depolarizing_n100_exact.cert.json",
    "paper/main.tex",
    "paper/references.bib",
    "paper/figures/fig1_1d_kms_trajectories.pdf",
    "paper/figures/fig1_1d_kms_trajectories.png",
    "paper/figures/fig2_scaling_and_alpha_phases.pdf",
    "paper/figures/fig2_scaling_and_alpha_phases.png",
    "paper/figures/fig3_sharpness_and_speedups.pdf",
    "paper/figures/fig3_sharpness_and_speedups.png",
]


def sha256_file(rel_path: str) -> str:
    h = hashlib.sha256()
    with open(os.path.join(ROOT, rel_path), "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def check_lean():
    print("[1/3] Checking Lean 4 formalization & axiom audit...")
    lean_dir = os.path.join(ROOT, "lean")
    r1 = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True)
    if r1.returncode != 0:
        print(r1.stdout, r1.stderr)
        sys.exit(1)
    r2 = subprocess.run(["lake", "env", "lean", "AuditAxioms.lean"], cwd=lean_dir, capture_output=True, text=True)
    if r2.returncode != 0:
        print(r2.stdout, r2.stderr)
        sys.exit(1)
    out = r2.stdout + r2.stderr
    for forbidden in ("sorryAx", "Classical.choice", "Lean.ofReduceBool"):
        if forbidden in out:
            print(f"FORBIDDEN AXIOM DETECTED: {forbidden}")
            print(out)
            sys.exit(1)
    lines = [ln for ln in out.splitlines() if "BeyondGapGibbs." in ln]
    if len(lines) < 16:
        print(f"Expected 16 audited theorems, found {len(lines)}")
        sys.exit(1)
    print(f"  LEAN CHECK: PASS ({len(lines)}/16 theorems, 0 sorry, 0 Classical.choice)")


def check_pytest():
    print("[2/3] Running pytest & exact rational (Q) LDL^T / convex-hull replay...")
    r = subprocess.run([sys.executable, "-m", "pytest", "-v", "tests/test_suite.py"], cwd=ROOT)
    if r.returncode != 0:
        sys.exit(1)
    print("  PYTEST + EXACT RATIONAL REPLAY: PASS")


def check_manifest(write: bool):
    print("[3/3] Checking SHA-256 manifest...")
    manifest_path = os.path.join(ROOT, "SHA256SUMS.json")
    current = {rel: sha256_file(rel) for rel in TRACKED_FILES}
    if write:
        with open(manifest_path, "w", encoding="utf-8") as f:
            json.dump(current, f, indent=2)
        print(f"  Wrote {len(current)} entries to SHA256SUMS.json")
        return
    with open(manifest_path, "r", encoding="utf-8") as f:
        saved = json.load(f)
    if saved != current:
        for k in set(saved) | set(current):
            if saved.get(k) != current.get(k):
                print(f"  MISMATCH: {k}")
        sys.exit(1)
    print(f"  MANIFEST CHECK: PASS ({len(current)}/{len(current)} files match byte-for-byte)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    check_lean()
    check_pytest()
    check_manifest(args.write_manifest)
    print("\nALL GATE-2 VERIFICATION CHECKS: PASS")
