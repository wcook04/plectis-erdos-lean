#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tamper checks for frozen original project provenance and official callers."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import check_frozen_fc_projects as frozen


class FrozenProjectTests(unittest.TestCase):
    project = "verification/FC249RationalObservable"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copytree(frozen.ROOT / self.project, self.root / self.project)
        self.binding_path = self.root / self.project / "source-binding.json"
        self.binding = json.loads(self.binding_path.read_text())

    def write_binding(self):
        self.binding_path.write_text(json.dumps(self.binding))

    def refresh(self, path):
        self.binding["package_sources"][path] = "sha256:" + hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        self.write_binding()

    def test_complete_original_project_passes_without_claiming_kernel_acceptance(self):
        result = frozen.check_project(self.root, self.project)
        self.assertEqual(result["original_lean_files"], 2)
        self.assertEqual(result["kernel_verification"], "not_established")

    def test_original_source_and_dependency_drift_are_rejected(self):
        for path in self.binding["source_closure"]:
            if not path.endswith(".lean"):
                continue
            with self.subTest(path=path):
                file = self.root / path; original = file.read_bytes()
                file.write_bytes(original + b"\n-- changed\n")
                with self.assertRaisesRegex(ValueError, "frozen bytes changed"):
                    frozen.check_project(self.root, self.project)
                file.write_bytes(original)

    def test_removing_dependency_from_manifest_and_disk_does_not_hide_import(self):
        path = next(path for path in self.binding["source_closure"] if path.endswith(".lean") and path != self.binding["source_path"])
        self.binding["source_closure"].pop(path); self.binding["source_path_origins"].pop(path)
        (self.root / path).unlink(); self.write_binding()
        with self.assertRaisesRegex(ValueError, "unresolved"):
            frozen.check_project(self.root, self.project)

    def test_environment_is_required_even_if_removed_from_manifest(self):
        path = self.project + "/lake-manifest.json"
        self.binding["source_closure"].pop(path); self.binding["source_path_origins"].pop(path)
        (self.root / path).unlink(); self.write_binding()
        with self.assertRaisesRegex(ValueError, "environment"):
            frozen.check_project(self.root, self.project)

    def test_symlink_cannot_supply_original_source(self):
        path = self.root / self.binding["source_path"]
        external = self.root / "outside.lean"; external.write_bytes(path.read_bytes())
        path.unlink(); path.symlink_to(external)
        with self.assertRaisesRegex(ValueError, "symlinked"):
            frozen.check_project(self.root, self.project)

    def test_unrecorded_cache_and_project_escape_are_rejected(self):
        (self.root / self.project / ".lake").mkdir()
        (self.root / self.project / ".lake" / "untrusted.olean").write_bytes(b"cache")
        with self.assertRaisesRegex(ValueError, "unrecorded"):
            frozen.check_project(self.root, self.project)
        with self.assertRaisesRegex(ValueError, "project path"):
            frozen.check_project(self.root, "verification/../outside")

    def test_unrecorded_directory_symlink_is_rejected(self):
        (self.root / self.project / "hidden").symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"):
            frozen.check_project(self.root, self.project)

    def test_drifted_selection_fails_even_when_package_hash_is_updated(self):
        path = next(path for path in self.binding["package_sources"] if path.endswith("comparator.json"))
        config = json.loads((self.root / path).read_text()); config["theorem_names"] = ["Other.result"]
        (self.root / path).write_text(json.dumps(config)); self.refresh(path)
        with self.assertRaisesRegex(ValueError, "selection"):
            frozen.check_project(self.root, self.project)

    def test_candidate_import_in_challenge_fails_even_when_hash_is_updated(self):
        path = next(path for path in self.binding["package_sources"] if path.endswith("Challenge.lean"))
        file = self.root / path; file.write_text(file.read_text().replace("import Mathlib", "import Mathlib\nimport " + self.binding["solution_module"]))
        self.refresh(path)
        with self.assertRaisesRegex(ValueError, "only Mathlib"):
            frozen.check_project(self.root, self.project)

    def test_nested_comments_do_not_invent_source_imports(self):
        self.assertEqual(frozen.imports("/- import Evil /- nested -/ -/\n-- import Other\nimport Mathlib\n"), ["Mathlib"])

    def test_dedicated_callers_bind_source_project_and_full_official_job(self):
        for entry, slug in [("FC257ReciprocalSupport", "fc257-reciprocal"), ("FC249RationalObservable", "fc249-rational"), ("FCMergedIntegerAdapters", "fc-merged-integer"), ("FC1041HausdorffCounterexample", "fc1041-hausdorff")]:
            text = (frozen.ROOT / ".github/workflows" / (slug + "-trusted-preflight.yml")).read_text()
            with self.subTest(entry=entry):
                self.assertIn("SOURCE_COMMIT: ${{ github.sha }}", text)
                self.assertIn("'project_path': 'verification/" + entry + "'", text)
                self.assertIn("PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@f49b4f29aa458fc70c3a4c8cadca9312adbdc559", text)
                self.assertIn("mode: full", text)
                self.assertNotIn("lake build", text)
                self.assertNotIn("actions/cache", text)


if __name__ == "__main__":
    unittest.main()
