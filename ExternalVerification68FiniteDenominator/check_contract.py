#!/usr/bin/env python3
"""Check this family's exact source/selection contract; does not execute Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

FAMILY = 'ExternalVerification68FiniteDenominator'
NS = 'Erdos249257.' + FAMILY
TARGET = NS + '.full_finite_denominator_exclusion'
DATA = 'ErdosProblems/Erdos68/PaperCompleteFiniteSizeData.lean'
PARAMETERS = '''(a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :'''
FULL = '''(2 : ℕ) ^ 39990 ≤ q ∧
      fareyLeftDenominator + fareyRightDenominator ≤ q ∧ (10 : ℕ) ^ 12040 < q'''
WEAK = '(2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q'
SERIES = "∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def theorem_type(text: str) -> str:
    parts = text.split('theorem full_finite_denominator_exclusion ')
    require(len(parts) == 2, 'exactly one selected theorem required')
    require(' := by\n' in parts[1], 'selected proof boundary missing')
    return parts[1].split(' := by\n', 1)[0]


def verify(files: dict[str, str], source: str) -> None:
    require(len(files['Challenge.lean'].encode()) <= 102400 and len(files['Challenge.lean'].splitlines()) <= 1000, 'Challenge exceeds the existing hard publication limit')
    require(source.count('def sizeFarey : FareyData := {') == 1, 'unique source witness required')
    tail = source.split('def sizeFarey : FareyData := {', 1)[1]
    rows = re.findall(r'^  (leftDen|rightDen) := (0x[0-9a-f]+)$', tail, re.M)
    require(len(rows) == 2 and {k for k, _ in rows} == {'leftDen', 'rightDen'}, 'exact source numeral fields required')
    numerals = dict(rows)
    for name in ['Challenge.lean', 'Solution.lean', 'NegativeSolution.lean']:
        text = files[name]
        imports = re.findall(r'^import (.+)$', text, re.M)
        require(imports == (['Mathlib'] if name == 'Challenge.lean' else ['ErdosProblems.Erdos68.PaperCompleteFiniteSizeCertificate']), name + ': import boundary changed')
        require(text.count(SERIES) == 1, name + ': literal series changed')
        for local, source_key in [('fareyLeftDenominator', 'leftDen'), ('fareyRightDenominator', 'rightDen')]:
            values = re.findall(r'def ' + local + r' : ℕ :=\n  (0x[0-9a-f]+)\n', text)
            require(values == [numerals[source_key]], name + ': numeral drift ' + local)
        expected = PARAMETERS + '\n    ' + (WEAK if name == 'NegativeSolution.lean' else FULL)
        require(theorem_type(text) == expected, name + ': selected statement changed')
    solution = files['Solution.lean'].split('theorem full_finite_denominator_exclusion ', 1)[1]
    proof = solution.split(' := by\n', 1)[1].split('\n\n', 1)[0]
    require(proof == '  exact ErdosProblems.Erdos68.PaperComplete.FiniteLead.SizeOnly.denominator_exclusion a q hq hS', 'full source consumer changed')
    require('sorry' not in files['Solution.lean'], 'solution cannot contain sorry')
    for name, module in [('comparator.json', 'Solution'), ('comparator-negative-mismatch.json', 'NegativeSolution')]:
        config = json.loads(files[name])
        require(config == {'challenge_module': FAMILY + '.Challenge', 'solution_module': FAMILY + '.' + module, 'theorem_names': [TARGET], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': True}, name + ': exact single-target config required')
    require(files['AxiomAudit.lean'] == 'import ' + FAMILY + '.Solution\n\n#print axioms ' + TARGET + '\n', 'audit must reach selected full endpoint')
    require(theorem_type(files['NegativeSolution.lean']) != theorem_type(files['Challenge.lean']), 'negative must drop the exact Farey conclusion')


def negative_controls(files: dict[str, str], source: str) -> list[str]:
    mutations = [
        ('hard_byte_limit', 'Challenge.lean', lambda s: s + ' ' * 102400),
        ('hard_line_limit', 'Challenge.lean', lambda s: s + '\n' * 1000),
        ('farey_digit', 'Challenge.lean', lambda s: s.replace('0x', '0xf', 1)),
        ('missing_conjunct', 'Challenge.lean', lambda s: s.replace('fareyLeftDenominator + fareyRightDenominator ≤ q ∧ ', '', 1)),
        ('extra_hypothesis', 'Challenge.lean', lambda s: s.replace('(hq : 0 < q)', '(hq : 0 < q) (hcertificate : True)', 1)),
        ('source_import', 'Challenge.lean', lambda s: s.replace('import Mathlib', 'import ErdosProblems.Erdos68.PaperCompleteFiniteSizeCertificate', 1)),
        ('old_projection_selection', 'comparator.json', lambda s: s.replace('full_finite_denominator_exclusion', 'finite_denominator_exclusion')),
        ('old_projection_audit', 'AxiomAudit.lean', lambda s: s.replace('full_finite_denominator_exclusion', 'finite_denominator_exclusion')),
        ('weakened_positive_solution', 'Solution.lean', lambda s: s.replace(FULL, WEAK, 1)),
    ]
    passed = []
    for label, name, mutate in mutations:
        candidate = dict(files)
        candidate[name] = mutate(candidate[name])
        require(candidate[name] != files[name], label + ': mutation failed')
        try:
            verify(candidate, source)
        except ValueError:
            passed.append(label)
        else:
            raise ValueError(label + ': corrupt candidate accepted')
    return passed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True, help='the retained source checkout whose twelve hashes match source_binding.json')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    family = Path(__file__).resolve().parent
    binding = json.loads((family / 'source_binding.json').read_text())
    for row in binding['source_modules']:
        require(sha((args.source_root / row['path']).read_bytes()) == row['sha256'], 'compiled source closure drift: ' + row['path'])
    for name, expected in binding['source_environment_sha256'].items():
        require(sha((args.source_root / name).read_bytes()) == expected, 'compiled source environment drift: ' + name)
    names = ['Challenge.lean', 'Solution.lean', 'NegativeSolution.lean', 'AxiomAudit.lean', 'comparator.json', 'comparator-negative-mismatch.json']
    files = {name: (family / name).read_text() for name in names}
    source = (args.source_root / DATA).read_text()
    verify(files, source)
    tests = negative_controls(files, source) if args.self_test else []
    print(json.dumps({'status': 'offline_contract_pass', 'selected_theorem': TARGET, 'source_modules_checked': len(binding['source_modules']), 'challenge_bytes': len(files['Challenge.lean'].encode()), 'negative_controls_rejected': tests, 'lean_run': False, 'comparator_run': False, 'nanoda_run': False}, indent=2))


if __name__ == '__main__':
    main()
