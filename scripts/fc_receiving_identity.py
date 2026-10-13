#!/usr/bin/env python3
"""Compare actual immutable FC declarations with candidate proofs on Linux.

The stock, pinned Comparator captures the actual FC challenge export before it
compiles the candidate under landrun. This helper never authors a Challenge.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

TOOLS = {
    "comparator": ("https://github.com/leanprover/comparator.git", "575674928e239f5bc452aab72d1dd7b0f1326494"),
    "lean4export": ("https://github.com/leanprover/lean4export.git", "a3e35a584f59b390667db7269cd37fca8575e4bf"),
    "landrun": ("https://github.com/zouuup/landrun.git", "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"),
    "nanoda": ("https://github.com/robsimmons/nanoda_lib.git", "68d5ca9db226849b41a6fff59d796ff19d0a8840"),
    # Historical confinement adapter only; this is a native stock Comparator
    # check, not the current PalomarSubmission official pipeline.
    "pipeline": ("https://github.com/PalomarRegistry/PalomarSubmission.git", "ef2fa1eadcb246c2346ddba39b52eaa53d4bb763"),
}
TARGETS = {
    "1049-order-coeff": ("", "FormalConjectures/Paper/ZudilinHankelInitialTerm.lean", "FormalConjectures.Paper.ZudilinHankelInitialTerm", "FC1049OrderCoeffCurrent", "FC1049OrderCoeffSolution", "ZudilinHankelInitialTerm.first_nonzero_term"),
    # Unsubmitted candidates require --receiving-commit after their exact FC
    # draft and immutable proof URL have been prepared. No default PR is implied.
    "243-nonintegral": ("", "FormalConjectures/ErdosProblems/243.lean", "FormalConjectures.ErdosProblems.243", "FC243NonintegralRateCurrent", "FCNonintegralRateSolutions", "Erdos243.erdos_243.variants.nonintegral_regular_rate"),
    "249-mixed": ("", "FormalConjectures/ErdosProblems/249.lean", "FormalConjectures.ErdosProblems.249", "FC249MixedModuliCurrent", "FC249MixedModuliSolution", "Erdos249.erdos_249.variants.rational_mixed_dyadic_observables"),
    "269-kernel": ("", "FormalConjectures/Paper/ThreePrimeRunningLcm.lean", "FormalConjectures.Paper.ThreePrimeRunningLcm", "FC269UniformKernelCurrent", "FC269UniformKernelSolution", "ThreePrimeRunningLcm.uniform_rank_and_nonseparation"),
    "68-liminf": ("", "FormalConjectures/Paper/FactorialCommonDenominator.lean", "FormalConjectures.Paper.FactorialCommonDenominator", "FC68CommonDenominatorCurrent", "FC68CommonDenominatorSolution", "FactorialCommonDenominator.growth_liminf"),
    "6579": ("e6bf75a53ef0655241873e5f12427fb6b4695de5", "FormalConjectures/ErdosProblems/249.lean", "FormalConjectures.ErdosProblems.249", "FC249RationalObservableCurrent", "FC249Repair", "Erdos249.erdos_249.variants.rational_dyadic_observable"),
    "6576": ("ba0edafdf1bc3b0ad3a563295503ef68751dc514", "FormalConjectures/ErdosProblems/1041.lean", "FormalConjectures.ErdosProblems.1041", "FC1041SharpGapCurrent", "FC6576Solution", "Erdos1041.erdos_1041.variants.sharp_collinear_gap"),
    "6577": ("38f435dab7ca2da901588a5e91e93452eaba8910", "FormalConjectures/ErdosProblems/249.lean", "FormalConjectures.ErdosProblems.249", "FC249CountableIndependenceCurrent", "FC6577Solution", "Erdos249.erdos_249.variants.least_residue_dilation_independence"),
    "6527": ("4139651cf87e3ec7893d6038e5d12173f075be66", "FormalConjectures/ErdosProblems/1049.lean", "FormalConjectures.ErdosProblems.1049", "FC1049ContourMeasureCurrent", "FC6527Solution", "Erdos1049.erdos_1049.variants.rational_base_contour_measure"),
    "6523-cubic": ("56710453a2af5ac017df557431aa238346e3a35b", "FormalConjectures/ErdosProblems/243.lean", "FormalConjectures.ErdosProblems.243", "FC243DualCurrent", "FC6523Solutions", "Erdos243.erdos_243.variants.cubic_rate"),
    "6523-product": ("56710453a2af5ac017df557431aa238346e3a35b", "FormalConjectures/ErdosProblems/243.lean", "FormalConjectures.ErdosProblems.243", "FC243DualCurrent", "FC6523Solutions", "Erdos243.erdos_243.variants.slow_growth_product_defect"),
    "6528-finite": ("40f7826a7ba761dd39b4542094d6149c60ce6c47", "FormalConjectures/ErdosProblems/257.lean", "FormalConjectures.ErdosProblems.257", "FC257WeightedSupportCurrent", "FC6528Solutions", "Erdos257.erdos_257.variants.finite_prime_weighted_support"),
    "6528-mixed": ("40f7826a7ba761dd39b4542094d6149c60ce6c47", "FormalConjectures/ErdosProblems/257.lean", "FormalConjectures.ErdosProblems.257", "FC257WeightedSupportCurrent", "FC6528Solutions", "Erdos257.erdos_257.variants.arbitrary_weight_mixed_support"),
    "6529": ("f5d7b003955c1418d5e962c781aa55ff322a2c16", "FormalConjectures/ErdosProblems/257.lean", "FormalConjectures.ErdosProblems.257", "FC257ReciprocalSupportCurrent", "FC6529Solution", "Erdos257.erdos_257.variants.summable_reciprocal_support"),
    "6780": ("009f3ca88924051271af89fc988e0d12e1fad23f", "FormalConjectures/Paper/GeometricMomentHankel.lean", "FormalConjectures.Paper.GeometricMomentHankel", "FC1049HankelCurrent", "FC6780Solution", "GeometricMomentHankel.fixed_base_asymptotic"),
    "6971-257": ("b47d6ce7ebabf79193826fad5b14b13e44f9c786", "FormalConjectures/ErdosProblems/257.lean", "FormalConjectures.ErdosProblems.257", "FCMergedIntegerAdaptersCurrent", "FC6971IntegerSolutions", "Erdos257.erdos_257.variants.tsum_top"),
    "6971-1049": ("b47d6ce7ebabf79193826fad5b14b13e44f9c786", "FormalConjectures/ErdosProblems/1049.lean", "FormalConjectures.ErdosProblems.1049", "FCMergedIntegerAdaptersCurrent", "FC6971IntegerSolutions", "Erdos1049.erdos_1049.variants.geq_2_integer"),
    "6971-258": ("b47d6ce7ebabf79193826fad5b14b13e44f9c786", "FormalConjectures/ErdosProblems/258.lean", "FormalConjectures.ErdosProblems.258", "FCMergedIntegerAdaptersCurrent", "FC6971IntegerSolutions", "Erdos258.erdos_258.variants.constant"),
    "6971-1041": ("b47d6ce7ebabf79193826fad5b14b13e44f9c786", "FormalConjectures/ErdosProblems/1041.lean", "FormalConjectures.ErdosProblems.1041", "FC1041HausdorffCurrent", "FC6971HausdorffSolution", "Erdos1041.erdos_1041"),
}
LIBRARY_ROOTS = {
    "243-nonintegral": {"ErdosProblems", "FCNonintegralRateSolutions"},
    "249-mixed": {"ErdosProblems", "FC249MixedModuliSolution"},
    "269-kernel": {"ErdosProblems", "FC269UniformKernelSolution"},
    "68-liminf": {"ErdosProblems", "Solutions", "FC68CommonDenominatorSolution"},
    "6579": {"ErdosProblems", "FC249Repair"},
    "6576": {"ErdosProblems", "ExternalVerification", "FC6576Solution"},
    "6577": {"ErdosProblems", "Solutions", "FC6577Solution"},
    "6527": {"ErdosProblems", "Solutions", "FC6527Solution"},
    "6523-cubic": {"ErdosProblems", "Solutions", "ExternalVerification", "FC6523Solutions"},
    "6523-product": {"ErdosProblems", "Solutions", "ExternalVerification", "FC6523Solutions"},
    "6528-finite": {"Erdos249257", "Erdos257PeriodNoncollapse", "ErdosProblems", "Solutions", "FC6528Solutions"},
    "6528-mixed": {"Erdos249257", "Erdos257PeriodNoncollapse", "ErdosProblems", "Solutions", "FC6528Solutions"},
    "6529": {"Erdos249257", "ErdosProblems", "ExternalVerification", "Solutions", "FormalConjecturesVariants", "FC6529Solution"},
    "6780": {"ErdosProblems", "Solutions", "FC6780Solution"},
    "6971-257": {"Erdos249257", "FormalConjecturesAdapter", "FC6971IntegerSolutions"},
    "6971-1049": {"Erdos249257", "FormalConjecturesAdapter", "FC6971IntegerSolutions"},
    "6971-258": {"Erdos249257", "FormalConjecturesAdapter", "FC6971IntegerSolutions"},
    "6971-1041": {"ErdosProblems", "FC6971HausdorffSolution"},
}
PIN = "leanprover/lean4:v4.33.1"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
BUILTINS = ["Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce"]
MARKERS = ["FC_RECEIVING_STATEMENT_AND_DEPENDENCIES_PASS", "FC_RECEIVING_AXIOM_CLOSURE_PASS", "FC_RECEIVING_DEFAULT_KERNEL_PASS", "FC_RECEIVING_POSITIVE_CONTROL_PASS", "FC_RECEIVING_NEGATIVE_CONTROL_REJECTED"]


def digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def run(argv, cwd: Path, log: Path, env=None, *, check=True):
    log.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(list(map(str, argv)), cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=19800)
    log.write_bytes(proc.stdout)
    print(f"{log.name}: exit {proc.returncode}", flush=True)
    if check and proc.returncode:
        raise RuntimeError(f"{log.name}: command failed with {proc.returncode}")
    return proc


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def checkout(url, commit, path: Path, out: Path):
    if path.exists():
        raise RuntimeError(f"refuse reused verifier workspace: {path}")
    path.mkdir(parents=True)
    run(["git", "init", path], path, out / f"{path.name}-init.log")
    run(["git", "remote", "add", "origin", url], path, out / f"{path.name}-remote.log")
    run(["git", "fetch", "--depth", "1", "origin", commit], path, out / f"{path.name}-fetch.log")
    run(["git", "checkout", "--detach", commit], path, out / f"{path.name}-checkout.log")
    if git(path, "rev-parse", "HEAD") != commit or git(path, "status", "--porcelain"):
        raise RuntimeError(f"immutable checkout failed: {path}")


def capture(path: Path, name: str, out: Path):
    data = path.read_bytes()
    (out / name).write_bytes(data)
    return digest(data)


def environment(project: Path, prefix: str, out: Path):
    manifest = json.loads((project / "lake-manifest.json").read_text())
    if (project / "lean-toolchain").read_text().strip() != PIN:
        raise RuntimeError("receiving Lean toolchain differs")
    mathlib = next(x for x in manifest["packages"] if x["name"] == "mathlib")
    if mathlib["rev"] != MATHLIB:
        raise RuntimeError("receiving Mathlib differs")
    return {
        "lean-toolchain": capture(project / "lean-toolchain", prefix + "-lean-toolchain", out),
        "lake-manifest.json": capture(project / "lake-manifest.json", prefix + "-lake-manifest.json", out),
    }


def execute(args):
    source, work, out = args.source.resolve(), args.work.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    default_receiving = TARGETS[args.unit][0]
    report = {"schema": "formal_conjectures_receiving_identity/1", "evidence_class": "actual_receiving_export_remote_native", "verified": False, "pull_request": int(args.unit.split("-", 1)[0]) if default_receiving else None, "stages": {}}
    try:
        if not re.fullmatch(r"[0-9a-f]{40}", args.source_commit):
            raise RuntimeError("source commit must be immutable")
        if git(source, "rev-parse", "HEAD") != args.source_commit or git(source, "status", "--porcelain"):
            raise RuntimeError("candidate checkout must be clean at exact event SHA")
        fc_commit, fc_path, canonical_module, package_name, solution_module, declaration = TARGETS[args.unit]
        if args.receiving_commit:
            if not re.fullmatch(r"[0-9a-f]{40}", args.receiving_commit):
                raise RuntimeError("receiving commit must be a full immutable SHA")
            fc_commit = args.receiving_commit
        if not re.fullmatch(r"[0-9a-f]{40}", fc_commit):
            raise RuntimeError("unsubmitted candidate requires an exact receiving commit")
        package_rel = "verification/" + package_name
        package = source / package_rel
        # String.toName needs escaping for numeric module segments only.
        challenge_module = ".".join("«" + part + "»" if part.isdecimal() else part for part in canonical_module.split("."))
        proof_rel = package_rel + "/" + solution_module + ".lean"
        proof_file = source / proof_rel
        if not proof_file.is_file():
            raise RuntimeError("selected proof package is absent")
        receiving = work / "receiving"
        checkout("https://github.com/google-deepmind/formal-conjectures.git", fc_commit, receiving, out)
        if (receiving / ".lake").exists():
            raise RuntimeError("receiving verifier must start without candidate artifacts")
        receiving_env = environment(receiving, "receiving", out)
        proof_env = environment(package, "proof", out)
        report["receiving"] = {"repository": "google-deepmind/formal-conjectures", "commit": fc_commit, "path": fc_path, "declaration": declaration, "project_path": "", "module": canonical_module, "lean_toolchain": PIN, "environment": receiving_env, "file_sha256": capture(receiving / fc_path, "receiving-target.lean", out)}
        report["proof"] = {"repository": "wcook04/plectis-erdos-lean", "commit": args.source_commit, "path": proof_rel, "declaration": declaration, "project_path": package_rel, "module": solution_module, "lean_toolchain": PIN, "environment": proof_env, "file_sha256": capture(proof_file, "proof-target.lean", out)}
        capture(package / "source-binding.json", "source-binding.json", out)
        report["helper_sha256"] = digest(Path(__file__).read_bytes())
        report["workflow"] = {"repository": os.environ["GITHUB_REPOSITORY"], "run_id": int(os.environ["GITHUB_RUN_ID"]), "run_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]), "head_sha": os.environ["GITHUB_SHA"], "path": ".github/workflows/fc-receiving-identity.yml"}
        if report["workflow"]["head_sha"] != args.source_commit:
            raise RuntimeError("workflow event and candidate source differ")
        report["tool_sources"] = {}
        for name, (url, rev) in TOOLS.items():
            root = work / name
            checkout(url, rev, root, out)
            report["tool_sources"][name] = {"repository": url.removesuffix(".git"), "commit": rev}
        env = dict(os.environ, LEAN_ABORT_ON_PANIC="1", ELAN_TOOLCHAIN=PIN)
        for toolchain in [PIN, "leanprover/lean4:v4.34.0-rc1"]:
            run(["elan", "toolchain", "install", toolchain], source, out / (toolchain.rsplit(":", 1)[1] + "-install.log"))
        run(["lake", "build", "lean4export"], work / "lean4export", out / "exporter-build.log", env)
        run(["lake", "build", "comparator"], work / "comparator", out / "comparator-build.log", dict(os.environ, ELAN_TOOLCHAIN="leanprover/lean4:v4.34.0-rc1"))
        run(["go", "build", "-o", work / "landrun-bin", "./cmd/landrun"], work / "landrun", out / "landrun-build.log", dict(os.environ, CGO_ENABLED="0"))
        run(["cargo", "+1.90.0", "build", "--release", "--locked", "--bin", "nanoda_bin"], work / "nanoda", out / "nanoda-build.log")
        exporter = work / "lean4export/.lake/build/bin/lean4export"
        comparator = work / "comparator/.lake/build/bin/comparator"
        prefix_proc = run(["lean", "--print-prefix"], receiving, out / "compiler-prefix.log", env)
        prefix = Path(prefix_proc.stdout.decode().strip())
        if not prefix.is_absolute() or not (prefix / "bin/lean").is_file():
            raise RuntimeError("invalid trusted compiler prefix")
        # Stock Comparator grants execution to the receiving compiler prefix.
        # Place the two additional trusted executables there before candidate
        # execution; the sandbox never grants this prefix write permission.
        real_exporter = prefix / "bin/fc-receiving-lean4export"
        if real_exporter.exists():
            raise RuntimeError("refuse reused exporter executable")
        real_exporter.write_bytes(exporter.read_bytes())
        real_exporter.chmod(0o755)
        proxy = prefix / "bin/fc-receiving-exporter-proxy"
        proxy_source = work / "exporter-proxy.go"
        proxy_source.write_text('package main\nimport "C"\nimport("bytes";"crypto/sha256";"fmt";"os";"os/exec")\nfunc main(){c:=exec.Command(' + json.dumps(str(real_exporter)) + ',os.Args[1:]...); var b bytes.Buffer;c.Stdout=&b;c.Stderr=os.Stderr;err:=c.Run();fmt.Fprintf(os.Stderr,"FC_EXPORT_BYTES %s sha256:%x\\n",os.Args[1],sha256.Sum256(b.Bytes()));os.Stdout.Write(b.Bytes());if err!=nil {fmt.Fprintf(os.Stderr,"FC_EXPORT_CHILD_ERROR %v\\n",err);if e,ok:=err.(*exec.ExitError);ok{os.Exit(e.ExitCode())};os.Exit(1)}}\n')
        capture(proxy_source, "exporter-proxy.go", out)
        run(["go", "build", "-o", proxy, proxy_source], source, out / "exporter-proxy-build.log", dict(os.environ, CGO_ENABLED="1"))
        # Both dynamic executables must use the same system loader. Stock
        # landrun --ldd then grants that loader through the native proxy itself.
        def elf_interpreter(binary, name):
            header = run(["readelf", "--program-headers", binary], source, out / (name + "-elf.log"))
            match = re.search(r"Requesting program interpreter: ([^\]]+)", header.stdout.decode())
            if not match:
                raise RuntimeError("trusted executable lacks a dynamic ELF interpreter: " + name)
            return match[1]
        proxy_interpreter = elf_interpreter(proxy, "exporter-proxy")
        if proxy_interpreter != elf_interpreter(real_exporter, "lean4export"):
            raise RuntimeError("proxy and trusted exporter use different ELF interpreters")
        report["exporter_proxy_elf_interpreter"] = proxy_interpreter
        if digest(real_exporter.read_bytes()) != digest(exporter.read_bytes()):
            raise RuntimeError("copied trusted exporter changed")
        report["exporter_proxy_sha256"] = digest(proxy.read_bytes())
        env.update(COMPARATOR_LEAN4EXPORT=str(proxy), COMPARATOR_LANDRUN=str(work / "landrun-bin"), COMPARATOR_NANODA=str(work / "nanoda/target/release/nanoda_bin"))
        for name, binary in [("lean4export", exporter), ("comparator", comparator), ("landrun", work / "landrun-bin"), ("nanoda", work / "nanoda/target/release/nanoda_bin")]:
            report["tool_sources"][name]["binary_sha256"] = digest(binary.read_bytes())
        report["tool_sources"]["lean4export"]["build_toolchain"] = PIN
        report["tools"] = {name + "_commit": rev for name, (_, rev) in TOOLS.items()}
        report["tools"]["lean4export_build_toolchain"] = PIN
        sys.path.insert(0, str(work / "pipeline/scripts"))
        from verify_submission import systemd_command
        def compare(config, log_name, expect_success=True, project=receiving):
            path = out / (log_name + ".json")
            path.write_text(json.dumps(config, indent=2) + "\n")
            argv = systemd_command([str(prefix / "bin/lake"), "env", str(comparator), str(path)], cwd=project, environment=env, timeout=19800)
            proc = run(argv, project, out / (log_name + ".log"), env, check=False)
            text = proc.stdout.decode(errors="replace")
            if expect_success and (proc.returncode or "Your solution is okay!" not in text or "Lean default kernel accepts the solution" not in text or "nanoda kernel accepts the solution" not in text):
                raise RuntimeError(f"{log_name}: stock Comparator rejected")
            return proc, text
        # Exercise the exact stock confinement launcher on trusted Init-only
        # source before hydrating/building FC or executing candidate source.
        smoke = work / "trusted-launcher-smoke"
        smoke.mkdir(exist_ok=False)
        (smoke / "lean-toolchain").write_text(PIN + "\n")
        (smoke / "lakefile.toml").write_text('name = "trusted_receiving_smoke"\n[[lean_lib]]\nname = "FCReceivingSmoke"\n')
        smoke_source = smoke / "FCReceivingSmoke.lean"
        smoke_source.write_text('import Init\ntheorem FCReceivingSmoke.smoke : True := True.intro\n')
        capture(smoke_source, "trusted-launcher-smoke.lean", out)
        compare({"challenge_module": "FCReceivingSmoke", "solution_module": "FCReceivingSmoke", "theorem_names": ["FCReceivingSmoke.smoke"], "permitted_axioms": AXIOMS, "enable_nanoda": True}, "trusted-launcher-smoke", project=smoke)
        report["trusted_launcher_smoke"] = {"status": "passed", "source": "trusted_helper_init_only", "candidate_executed": False}
        # Add only library search roots to the trusted receiving Lakefile. The actual
        # FC source and its toolchain/manifest are preserved byte for byte.
        lake = receiving / "lakefile.toml"
        original_lake = lake.read_bytes()
        (out / "receiving-lakefile.original.toml").write_bytes(original_lake)
        libraries = tomllib.loads((package / "lakefile.toml").read_text())["lean_lib"]
        with lake.open("a") as f:
            for lib in libraries:
                if set(lib) - {"name", "srcDir", "globs"}:
                    raise RuntimeError("unexpected candidate library options")
                if lib["name"] not in LIBRARY_ROOTS[args.unit]:
                    raise RuntimeError("candidate library root was not reviewed for this package")
                if any(g != lib["name"] and not g.startswith(lib["name"] + ".") for g in lib.get("globs", [lib["name"]])):
                    raise RuntimeError("candidate globs may not shadow trusted modules")
                directory = (package / lib.get("srcDir", ".")).resolve()
                if not directory.is_relative_to(package):
                    raise RuntimeError("candidate source root escaped package")
                f.write("\n[[lean_lib]]\nname = " + json.dumps(lib["name"]) + "\nsrcDir = " + json.dumps(str(directory)) + "\n")
                if "globs" in lib:
                    f.write("globs = " + json.dumps(lib["globs"]) + "\n")
            f.write('\n[[lean_lib]]\nname = "FCReceivingNegative"\n')
        capture(lake, "receiving-lakefile.validation.toml", out)
        run(["lake", "exe", "cache", "get"], receiving, out / "receiving-cache.log", env)
        def dependency_heads():
            lock = json.loads((receiving / "lake-manifest.json").read_text())
            heads = {}
            for dependency in lock["packages"]:
                root = receiving / ".lake/packages" / dependency["name"]
                if git(root, "rev-parse", "HEAD") != dependency["rev"] or git(root, "status", "--porcelain", "--untracked-files=all"):
                    raise RuntimeError("dependency source differs: " + dependency["name"])
                heads[dependency["name"]] = dependency["rev"]
            return heads
        report["dependency_commits"] = dependency_heads()
        run(["lake", "--wfail", "build", challenge_module], receiving, out / "actual-fc-build.log", env)
        # Retain the actual challenge before ANY candidate module is compiled.
        export_targets = [*BUILTINS, declaration, *AXIOMS, *PRIMITIVES]
        def export(module, filename):
            proc = subprocess.run(["lake", "env", str(proxy), module, "--", *export_targets], cwd=receiving, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=19800)
            (out / (filename + ".stderr.log")).write_bytes(proc.stderr)
            (out / filename).write_bytes(proc.stdout)
            if proc.returncode:
                raise RuntimeError(f"export failed: {module}")
            for line in proc.stdout.splitlines():
                json.loads(line)
            return digest(proc.stdout)
        challenge_digest = export(challenge_module, "challenge.export")
        report["challenge_export"] = {"path": "challenge.export", "sha256": challenge_digest, "captured_before_solution": True}
        config = {"challenge_module": challenge_module, "solution_module": solution_module, "theorem_names": [declaration], "permitted_axioms": AXIOMS, "enable_nanoda": True}
        _, actual_log = compare(config, "actual-receiving-comparator")
        actual_exports = dict(re.findall(r"^FC_EXPORT_BYTES (\S+) (sha256:[0-9a-f]{64})$", actual_log, re.M))
        if actual_exports.get(challenge_module) != challenge_digest:
            raise RuntimeError("stock Comparator consumed a different actual FC export")
        solution_digest = export(solution_module, "solution.export")
        if actual_exports.get(solution_module) != solution_digest:
            raise RuntimeError("stock Comparator consumed a different Solution export")
        report["stock_consumed_exports"] = actual_exports
        report["solution_export"] = {"path": "solution.export", "sha256": solution_digest}
        report["export_sha256"] = {"challenge": challenge_digest, "solution": solution_digest}
        for name in ["statement_and_dependencies", "axioms", "lean_default", "nanoda"]:
            report["stages"][name] = "passed"
        # Positive control reuses the accepted source as its own Challenge; it
        # checks the trusted driver/toolchain without adding an authored theorem.
        compare(dict(config, challenge_module=solution_module), "positive-control")
        (receiving / "FCReceivingNegative.lean").write_text(f"import Mathlib\ntheorem {declaration} : True := by trivial\n")
        proc, text = compare(dict(config, solution_module="FCReceivingNegative"), "negative-control", False)
        expected = "Challenge and solution theorem statement do not match: '" + declaration + "'"
        if proc.returncode == 0 or expected not in text:
            raise RuntimeError("negative control did not reach exact statement mismatch")
        report["stages"].update(positive_control="passed", negative_control="passed")
        report["controls"] = {"positive": {"status": "passed", "kind": "accepted_source_against_itself"}, "negative": {"status": "passed", "kind": "exact_selected_theorem_type_mismatch", "diagnostic": expected}}
        # Both selected immutable files and receiving definitions remain exact.
        if digest((receiving / fc_path).read_bytes()) != report["receiving"]["file_sha256"] or digest(proof_file.read_bytes()) != report["proof"]["file_sha256"]:
            raise RuntimeError("selected source changed during verification")
        if environment(receiving, "receiving-final", out) != receiving_env or environment(package, "proof-final", out) != proof_env:
            raise RuntimeError("environment changed during verification")
        if git(source, "rev-parse", "HEAD") != args.source_commit or git(source, "status", "--porcelain"):
            raise RuntimeError("candidate source changed during verification")
        report["preparation_boundary"] = {"status": "passed", "actual_receiving_source": True, "fresh_candidate_dependencies": True, "stock_comparator_challenge_export_before_sandboxed_solution": True, "solution_writable_paths": [str(receiving / ".lake")], "systemd_restrict_address_families": "~AF_UNIX"}
        if dependency_heads() != report["dependency_commits"]:
            raise RuntimeError("dependency source changed during verification")
        report["verified"] = True
        report["stage_results"] = report["stages"]
        report["stages"] = MARKERS
        report["status"] = "pass"
        report["source_commit"] = args.source_commit
        report["unit_id"] = args.unit
        report["name_mapping"] = "selected_theorem_name_only"
        report["kernel_acceptance"] = {"lean_default": True, "nanoda": True}
        report["preparation"] = "actual_receiving_export_before_isolated_solution_execution"
        for marker in MARKERS:
            print(marker, flush=True)
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = str(exc)
        raise
    finally:
        report["artifact_files"] = {str(p.relative_to(out)): digest(p.read_bytes()) for p in sorted(out.rglob("*")) if p.is_file() and p.name != "report.json"}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--unit", choices=TARGETS, default="6579")
    parser.add_argument("--receiving-commit", default="", help="Exact FC commit override; declaration and environment remain constrained")
    execute(parser.parse_args())
