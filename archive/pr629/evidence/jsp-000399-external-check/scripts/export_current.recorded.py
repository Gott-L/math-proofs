"""Export explicitly named roots from the freshly compiled current JSP399 packet.

This driver records exporter evidence only; it does not run an external checker.
It never compiles or changes the proof modules or installs dependencies.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent
FRESH = ROOT / "proof-fresh"
EXPORTER = ROOT / "exporter"
PACKET = ROOT.parent / "awards/evidence/jsp-000399-parametric-27"
PROOF_COMMIT = "86cf6d9a47a7134e9901c6464322eafddc89742e"
EXPECTED = {
    "Jsp399TripleCore": "ec6d0d0bf114c025bbcd5a82a77d3b0401433a2df630438a3f60e602f76b7ee4",
    "Jsp399Witness": "4f1937d3fe11b213adb5fe3301e0bb0fd546238063993521fd26ca32da525503",
    "EncodedCoeffCertificate": "2d64c4d56c8963a45597d8f933fb71e08b0d8e3f08f7a6ff057c588faaa94f23",
    "Jsp399Parametric": "fd486be111060dafac013d577fc75152b4ff1139187f5def7332efd15d832e77",
}
ENUMERATION = ["JSP399TwentySeven." + x for x in
               ["triples_complete", "triples_nodup", "triples_length"]]
ENDPOINTS = ["JSP399Parametric." + x for x in [
    "vector_triple_sums_perm", "every_additive_image_collision",
    "every_parameter_collision", "every_translated_parameter_collision",
    "example_is_nontrivial_collision",
]]
BRIDGES = ["JSP399Parametric.exampleA_matches",
           "JSP399Parametric.exampleB_matches_reverse"]


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", "utf-8")


def provenance(stage):
    published = {}
    for module, expected in EXPECTED.items():
        source = PACKET / (module + ".lean")
        actual = sha(source)
        if actual != expected:
            raise RuntimeError(f"Published source identity changed: {module}")
        published[module + ".lean"] = {"sha256": actual, "bytes": source.stat().st_size}
    receipt_path = ROOT / ("proof-serial-receipt.json" if stage != "core"
                           else "proof-fresh-receipt.json")
    receipt = json.loads(receipt_path.read_text("utf-8"))
    if stage != "core" and receipt.get("all_four_modules_passed") is not True:
        raise RuntimeError("Full stage requires the completed fresh four-module build")
    required = list(EXPECTED) if stage != "core" else ["Jsp399TripleCore"]
    compiled = {}
    for module in required:
        rows = [x for x in receipt["fresh_modules"] if x["module"] == module]
        if len(rows) != 1 or rows[0]["exit_code"] != 0:
            raise RuntimeError(f"Missing successful fresh build for {module}")
        row = rows[0]
        if "--trust=0" not in row["command"]:
            raise RuntimeError(f"Fresh build lacks required trust level: {module}")
        if row["source_sha256"] != EXPECTED[module]:
            raise RuntimeError(f"Build receipt source mismatch: {module}")
        source = FRESH / (module + ".lean")
        binary = FRESH / (module + ".olean")
        if sha(source) != EXPECTED[module] or sha(binary) != row["olean_sha256"]:
            raise RuntimeError(f"Fresh artifacts no longer match receipt: {module}")
        compiled[module] = {"source_sha256": sha(source), "olean_sha256": sha(binary),
                            "olean_bytes": binary.stat().st_size}
    gate_path = EXPORTER / ("lowering-result.json" if stage == "lowered" else "gate-result.json")
    gate = json.loads(gate_path.read_text("utf-8"))
    exporter = {}
    source_files = ["Export.lean", "Main.lean", "lean419.patch"]
    if stage == "lowered":
        if gate.get("all_seven_rfl_equalities_kernel_checked") is not True:
            raise RuntimeError("String lowering lacks its seven kernel-checked equality gates")
        source_files += ["string-lowering.patch", "StringLoweringCases.lean"]
    for filename in source_files:
        actual = sha(EXPORTER / filename)
        if actual != gate["source_and_patch_sha256"][filename]:
            raise RuntimeError(f"Exporter source changed since gate: {filename}")
        exporter[filename] = actual
    for filename in ["Export.olean", "Main.olean"]:
        actual = sha(EXPORTER / filename)
        if actual != gate["artifact_sha256"][filename]:
            raise RuntimeError(f"Exporter artifact changed since gate: {filename}")
        exporter[filename] = actual
    return {"published_sources": published, "fresh_modules_used": compiled,
            "fresh_build_receipt": receipt_path.name,
            "fresh_build_receipt_sha256": sha(receipt_path),
            "exporter_gate_sha256": sha(gate_path), "exporter_sha256": exporter}


def inventory(path, roots, expected_exporter_name):
    names = {0: ""}
    exprs = set()
    declarations = []
    by_name = {}
    string_literals = 0
    metadata = None
    row_count = 0
    with path.open("r", encoding="utf-8") as stream:
        for line_no, line in enumerate(stream, 1):
            row = json.loads(line)
            row_count += 1
            if line_no == 1:
                metadata = row["meta"]
            if "in" in row:
                if row["in"] != len(names):
                    raise RuntimeError(f"Noncontinuous name reference on line {line_no}")
                info = row.get("str", row.get("num"))
                suffix = info["str"] if "str" in row else str(info["i"])
                names[row["in"]] = ".".join(x for x in
                                               [names[info["pre"]], suffix] if x)
            if "ie" in row:
                if row["ie"] in exprs:
                    raise RuntimeError(f"Duplicate expression index on line {line_no}")
                exprs.add(row["ie"])
            string_literals += "strVal" in row
            groups = [(kind, row[kind]) for kind in
                      ["thm", "def", "axiom", "opaque", "quot"] if kind in row]
            if "inductive" in row:
                for key, kind in [("types", "inductive"), ("ctors", "constructor"),
                                  ("recs", "recursor")]:
                    groups.extend((kind, x) for x in row["inductive"][key])
            for kind, obj in groups:
                name = names[obj["name"]]
                if name in by_name:
                    raise RuntimeError(f"Repeated declaration: {name}")
                entry = {"kind": kind, "name": name, "line": line_no,
                         "name_reference": obj["name"], "type_reference": obj["type"]}
                if "value" in obj:
                    entry["value_reference"] = obj["value"]
                if "levelParams" in obj:
                    entry["level_parameters"] = [names[i] for i in obj["levelParams"]]
                declarations.append(entry)
                by_name[name] = entry
    if metadata["lean"]["version"] != "4.19.0":
        raise RuntimeError("Unexpected Lean export version")
    if metadata["format"]["version"] != "3.1.0":
        raise RuntimeError("Unexpected export format")
    if metadata["exporter"]["name"] != expected_exporter_name:
        raise RuntimeError("Unexpected exporter identity")
    selected = []
    for root in roots:
        entry = by_name.get(root)
        if not entry or entry["kind"] != "thm":
            raise RuntimeError(f"Root is missing or not a theorem: {root}")
        if entry["type_reference"] not in exprs or entry.get("value_reference") not in exprs:
            raise RuntimeError(f"Root type/value reference absent: {root}")
        selected.append(entry)
    return {"metadata": metadata, "json_rows": row_count, "names": len(names),
            "expressions": len(exprs), "string_literal_records": string_literals,
            "declaration_count": len(declarations), "roots": selected,
            "axioms": [x["name"] for x in declarations if x["kind"] == "axiom"],
            "declarations": declarations}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", choices=["core", "full", "lowered"], required=True)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    lean = Path(args.lean).resolve()
    roots = ENUMERATION if args.stage == "core" else ENUMERATION + ENDPOINTS + BRIDGES
    module = "Jsp399TripleCore" if args.stage == "core" else "Jsp399Parametric"
    evidence = provenance(args.stage)
    destination = ROOT / ("exports-" + args.stage)
    destination.mkdir(exist_ok=True)
    output = destination / "export.ndjson"
    if output.exists():
        raise RuntimeError("Refusing to overwrite an existing export; preserve the earlier run")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(FRESH), str(EXPORTER)])
    command = [str(lean), "--trust=0", "-s", "65536", "-j", "1", "-DElab.async=false",
               "--run", str(EXPORTER / "Main.lean"), module, "--", "--"] + roots
    record = {"stage": args.stage, "proof_repository": "Gott-L/awards",
              "proof_commit": PROOF_COMMIT, "proof_packet": "evidence/jsp-000399-parametric-27",
              "roots_requested": roots, "module": module, **evidence,
              "export_driver_sha256": sha(Path(__file__)),
              "lean_binary_sha256": sha(lean), "command": command,
              "maximum_export_bytes": 100 * 1024 * 1024,
              "external_checker_run": False, "external_checker_pass": False,
              "entire_packet_checked": False}
    if record["lean_binary_sha256"] != json.loads((EXPORTER / "gate-result.json").read_text("utf-8"))["lean_binary_sha256"]:
        raise RuntimeError("Lean executable differs from successful exporter gate")
    start = time.monotonic()
    failures = []
    total = [0]
    with (destination / "export.stderr.log").open("wb") as err:
        process = subprocess.Popen(command, cwd=EXPORTER, env=env,
                                   stdout=subprocess.PIPE, stderr=err)

        def pump():
            try:
                with output.open("xb") as out:
                    while chunk := process.stdout.read(65536):
                        if total[0] + len(chunk) > record["maximum_export_bytes"]:
                            failures.append("export exceeded 100 MiB hard cap")
                            process.kill()
                            return
                        out.write(chunk)
                        total[0] += len(chunk)
            except Exception as exc:
                failures.append(str(exc))
                process.kill()

        reader = threading.Thread(target=pump, daemon=True)
        reader.start()
        try:
            code = process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            failures.append("export timeout")
            process.kill()
            code = process.wait()
        reader.join(timeout=30)
        if reader.is_alive():
            failures.append("output reader did not terminate")
    record.update(export_exit_code=code, elapsed_seconds=round(time.monotonic()-start, 3),
                  export_bytes=output.stat().st_size, export_sha256=sha(output),
                  stderr_sha256=sha(destination / "export.stderr.log"),
                  checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    if code != 0:
        failures.append("exporter exited unsuccessfully")
    if not failures:
        try:
            expected_exporter_name = ("lean4export-lean4.19-string-lowered" if args.stage == "lowered"
                                      else "lean4export-lean4.19-backport")
            details = inventory(output, roots, expected_exporter_name)
            write_json(destination / "declaration-inventory.json", details)
            record.update({k: details[k] for k in ["metadata", "json_rows", "names",
                "expressions", "string_literal_records", "declaration_count", "roots", "axioms"]})
            record["inventory_sha256"] = sha(destination / "declaration-inventory.json")
            if details["string_literal_records"]:
                failures.append("string literal compatibility not established")
        except Exception as exc:
            failures.append("inventory validation: " + str(exc))
    record["export_gate_passed"] = not failures
    record["failures"] = failures
    record["scope_label"] = ("Current submitted enumeration lemmas exported; collision endpoints not exported"
        if args.stage == "core" else "Ten current packet roots exported; independent checking remains pending")
    write_json(destination / "export-result.json", record)
    print(json.dumps({k: record[k] for k in ["stage", "export_gate_passed", "export_exit_code",
          "export_bytes", "export_sha256", "scope_label", "failures"]}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
