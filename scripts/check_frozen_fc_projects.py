#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check frozen original source bytes and their isolated local import closure.

This checks packaging and provenance declarations. Kernel acceptance requires a
fresh full official verification report for the selected immutable host commit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = {"Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop", "Qq",
            "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient"}


def strip_comments(text: str) -> str:
    output, depth, quoted, escaped, i = [], 0, False, False, 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  "); i += 2; continue
            if pair == "-/":
                depth -= 1
                output.extend("  "); i += 2; continue
            output.append("\n" if text[i] == "\n" else " ")
            i += 1; continue
        if not quoted and pair == "/-":
            depth = 1
            output.extend("  "); i += 2; continue
        if not quoted and pair == "--":
            while i < len(text) and text[i] != "\n":
                output.append(" "); i += 1
            continue
        char = text[i]
        output.append(char)
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        i += 1
    if depth:
        raise ValueError("unterminated Lean comment")
    return "".join(output)


def regular(root: Path, relative: str) -> Path:
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts or ".lake" in rel.parts:
        raise ValueError(f"unsafe source path: {relative}")
    path = root / rel
    for parent in [path, *path.parents]:
        if parent == root.parent:
            break
        if parent.is_symlink():
            raise ValueError(f"symlinked source path: {relative}")
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"missing source path: {relative}")
    return path


def imports(body: str) -> list[str]:
    return [module for line in re.findall(
        r"^(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)", strip_comments(body), re.M)
        for module in line.split()]


def reachable_sources(project: Path, entry_path: str) -> set[str]:
    config = tomllib.loads(regular(project, "lakefile.toml").read_text())
    libraries = config.get("lean_lib", [])
    source_roots = {project, *(project / library.get("srcDir", ".") for library in libraries)}

    def claims(library: dict, module: str) -> bool:
        roots = library.get("roots", [library["name"]])
        globs = library.get("globs", roots)
        return any(module == root or module.startswith(root + ".") for root in roots) or any(
            module == glob or
            (glob.endswith(".*") and (module == glob[:-2] or module.startswith(glob[:-1]))) or
            (glob.endswith(".+") and module.startswith(glob[:-1])) for glob in globs)

    pending, seen = [regular(project, entry_path)], set()
    while pending:
        path = pending.pop()
        relative = path.relative_to(project).as_posix()
        if relative in seen:
            continue
        seen.add(relative)
        for module in imports(path.read_text()):
            if not re.fullmatch(r"[A-Za-z_][\w.]*", module):
                raise ValueError(f"unsupported import: {module}")
            if module.split(".")[0] in EXTERNAL:
                continue
            owners = [project / library.get("srcDir", ".")
                      for library in libraries if claims(library, module)]
            candidates = [root / (module.replace(".", "/") + ".lean")
                          for root in owners[-1:] or source_roots]
            found = [path for path in candidates if path.is_file()]
            if len(found) != 1:
                raise ValueError(f"unresolved or ambiguous local import: {module}")
            pending.append(regular(project, found[0].relative_to(project).as_posix()))
    return seen


def check_project(root: Path, project_path: str) -> dict:
    if not re.fullmatch(r"verification/FC[A-Za-z0-9]+", project_path):
        raise ValueError("invalid isolated project path")
    project = root / project_path
    binding = json.loads(regular(project, "source-binding.json").read_text())
    if (binding.get("schema") != "frozen_fc_project_binding/1"
            or binding.get("repository") != "wcook04/plectis-erdos-lean"
            or binding.get("original_repository") != "wcook04/plectis-erdos"
            or binding.get("project_path") != project_path
            or not re.fullmatch(r"[0-9a-f]{40}", binding.get("original_commit", ""))):
        raise ValueError("invalid frozen project identity")
    closure, origins = binding["source_closure"], binding["source_path_origins"]
    required_environment = {"lakefile.toml", "lake-manifest.json", "lean-toolchain", "LICENSE", "README.md"}
    if not required_environment.issubset(origins.values()):
        raise ValueError("complete original project environment is required")
    if binding.get("source_path") != project_path + "/" + binding.get("original_source_path", ""):
        raise ValueError("selected source differs from original layout")
    if set(closure) & set(binding["package_sources"]):
        raise ValueError("original files cannot be verification package sources")
    if set(closure) != set(origins):
        raise ValueError("every original file requires an exact source origin")
    for path, origin in origins.items():
        if path != project_path + "/" + origin:
            raise ValueError("original relative source layout changed")
    for path, digest in {**closure, **binding["package_sources"]}.items():
        if not path.startswith(project_path + "/"):
            raise ValueError("manifest source escapes isolated project")
        data = regular(root, path).read_bytes()
        if digest != "sha256:" + hashlib.sha256(data).hexdigest():
            raise ValueError(f"frozen bytes changed: {path}")
    if regular(project, "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.29.1":
        raise ValueError("reviewed historical toolchain changed")
    config_path = next(path for path in binding["package_sources"] if path.endswith("/comparator.json"))
    config = json.loads(regular(root, config_path).read_text())
    if (config.get("solution_module") != binding["solution_module"]
            or config.get("challenge_module") != binding["challenge_module"]
            or config.get("theorem_names") != binding["selected_declarations"]
            or config.get("enable_nanoda") is not True
            or set(config.get("permitted_axioms", [])) != {"propext", "Quot.sound", "Classical.choice"}
            or config.get("definition_names", [])):
        raise ValueError("verification selection or kernel policy changed")
    challenge_path = next(path for path in binding["package_sources"] if path.endswith("/Challenge.lean"))
    if imports(regular(root, challenge_path).read_text()) != ["Mathlib"]:
        raise ValueError("independent Challenge must import only Mathlib")
    reachable = reachable_sources(project, binding["original_source_path"])
    recorded = {origin for origin in origins.values() if origin.endswith(".lean")}
    if reachable != recorded:
        raise ValueError("manifest differs from the complete reachable original import closure")
    expected = {path.removeprefix(project_path + "/") for path in closure | binding["package_sources"]}
    expected.add("source-binding.json")
    all_paths = list(project.rglob("*"))
    if any(path.is_symlink() for path in all_paths):
        raise ValueError("isolated project contains a symlink")
    actual = {path.relative_to(project).as_posix() for path in all_paths if path.is_file()}
    if actual != expected:
        raise ValueError("isolated project contains missing or unrecorded files")
    return {"project_path": project_path, "original_commit": binding["original_commit"],
            "original_lean_files": len(reachable), "selected_declarations": binding["selected_declarations"],
            "status": "source_packaging_passed", "kernel_verification": "not_established"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"verification/FC[A-Za-z0-9]+", args.project):
        parser.error("project must name one isolated frozen FC project")
    print(json.dumps(check_project(ROOT, args.project), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
