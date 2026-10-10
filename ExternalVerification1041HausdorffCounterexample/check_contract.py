#!/usr/bin/env python3
"""Verify the exact source and selected statement; this does not run Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

FAMILY = "ExternalVerification1041HausdorffCounterexample"
TARGET = "Erdos249257." + FAMILY + ".preconnected_hausdorff_counterexample"
SOURCE_IMPORT = "ErdosProblems.Erdos1041.Counterexample.HausdorffLength"
FULL = """∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K →
          K ⊆ {z : ℂ | ‖p.eval z‖ < 1} →
          (2 : ℝ≥0∞) < μH[1] K"""
WEAK = FULL.replace(" ∧ p.roots.Nodup", "")
NAMES = ("Challenge.lean", "Solution.lean", "NegativeSolution.lean",
         "AxiomAudit.lean", "comparator.json", "comparator-negative-mismatch.json")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def statement(content: str) -> str:
    key = "theorem preconnected_hausdorff_counterexample :\n    "
    require(content.count(key) == 1, "selected theorem must occur exactly once")
    tail = content.split(key, 1)[1]
    require(" := by\n" in tail, "selected theorem proof boundary missing")
    return tail.split(" := by\n", 1)[0]


def verify(files: dict[str, str], source: str) -> None:
    require("theorem erdos1041_counterexample_hausdorff :" in source,
            "source preconnected theorem absent")
    challenge = files["Challenge.lean"]
    require(len(challenge.encode()) <= 102400 and len(challenge.splitlines()) <= 1000,
            "Challenge exceeds publication hard limits")
    imports = lambda s: re.findall(r"^import (.+)$", s, re.M)
    require(imports(challenge) == ["Mathlib"], "Challenge must depend on Mathlib only")
    for name in ("Solution.lean", "NegativeSolution.lean"):
        require(imports(files[name]) == ["Mathlib", SOURCE_IMPORT],
                name + ": source import changed")
        require("sorry" not in files[name], name + ": sorry forbidden")
        require("exact Erdos1041.Counterexample.erdos1041_counterexample_hausdorff" in files[name],
                name + ": exact source theorem consumer absent")
    require(statement(challenge) == FULL, "Challenge theorem changed")
    require(statement(files["Solution.lean"]) == FULL, "Solution theorem changed")
    require(statement(files["NegativeSolution.lean"]) == WEAK,
            "NegativeSolution must drop only root Nodup")
    for name, module in (("comparator.json", "Solution"),
                         ("comparator-negative-mismatch.json", "NegativeSolution")):
        require(json.loads(files[name]) == {
            "challenge_module": FAMILY + ".Challenge",
            "solution_module": FAMILY + "." + module,
            "theorem_names": [TARGET],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": True,
        }, name + ": selection changed")
    require(files["AxiomAudit.lean"] ==
            "import " + FAMILY + ".Solution\n\n#print axioms " + TARGET + "\n",
            "AxiomAudit must print the selected theorem")


def negative_controls(files: dict[str, str], source: str) -> list[str]:
    mutations = (
        ("missing_hausdorff_bound", "Challenge.lean",
         lambda x: x.replace("(2 : ℝ≥0∞) < μH[1] K", "True", 1)),
        ("weak_positive_solution", "Solution.lean",
         lambda x: x.replace(" ∧ p.roots.Nodup", "", 1)),
        ("source_import", "Challenge.lean",
         lambda x: x.replace("import Mathlib", "import " + SOURCE_IMPORT, 1)),
        ("extra_hypothesis", "Challenge.lean",
         lambda x: x.replace("∃ (p : ℂ[X])", "True → ∃ (p : ℂ[X])", 1)),
        ("wrong_selection", "comparator.json",
         lambda x: x.replace("preconnected_hausdorff_counterexample", "degreeSevenCounterexample", 1)),
        ("wrong_audit", "AxiomAudit.lean",
         lambda x: x.replace("preconnected_hausdorff_counterexample", "degreeSevenCounterexample", 1)),
        ("challenge_byte_limit", "Challenge.lean", lambda x: x + " " * 102400),
    )
    passed = []
    for label, name, mutate in mutations:
        candidate = dict(files)
        candidate[name] = mutate(candidate[name])
        require(candidate[name] != files[name], label + ": mutation ineffective")
        try:
            verify(candidate, source)
        except ValueError:
            passed.append(label)
        else:
            raise ValueError(label + ": corruption accepted")
    return passed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    root = args.source_root
    family = Path(__file__).resolve().parent
    binding = json.loads((family / "source_binding.json").read_text())
    require(binding["selected_theorem"] == TARGET, "bound selection changed")
    for row in binding["source_modules"]:
        require(sha(root / row["path"]) == row["sha256"],
                "source closure drift: " + row["path"])
    for name, expected in binding["source_environment_sha256"].items():
        require(sha(root / name) == expected, "source environment drift: " + name)
    files = {name: (family / name).read_text() for name in NAMES}
    source = (root / "ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean").read_text()
    verify(files, source)
    tests = negative_controls(files, source) if args.self_test else []
    print(json.dumps({"status": "offline_contract_pass", "selected_theorem": TARGET,
                      "source_modules_checked": len(binding["source_modules"]),
                      "negative_controls_rejected": tests, "lean_run": False,
                      "comparator_run": False, "nanoda_run": False}, indent=2))


if __name__ == "__main__":
    main()
