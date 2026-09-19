"""Compare declaration types/bodies modulo the seven literal expansions.

This structural audit is independent of the exporter driver and does not replace
kernel checking. Reference numbers may change, so expression DAGs are hashed
bottom-up after applying the reviewed expansion to the original literal nodes.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PILOT = ROOT.parent


def h(value):
    return hashlib.sha256(json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()


def named(name):
    value = h(["anonymous"])
    for part in name.split("."):
        value = h(["name_str", value, part])
    return value


ZERO = h(["zero"])


def const(name, levels=()):
    return h(["const", named(name), list(levels)])


def app(fn, arg):
    return h(["app", fn, arg])


def lowered_literal(text):
    char = const("Char")
    result = app(const("List.nil", (ZERO,)), char)
    for char_value in reversed(text):
        # Lean 4.19 Expr.lean:726 mkNatLit is frontend OfNat.ofNat,
        # not mkRawNatLit. Match the actual reviewed exporter construction.
        raw = h(["natVal", str(ord(char_value))])
        natural = app(app(app(const("OfNat.ofNat", (ZERO,)), const("Nat")), raw),
                      app(const("instOfNatNat"), raw))
        cell = app(const("Char.ofNat"), natural)
        result = app(app(app(const("List.cons", (ZERO,)), char), cell), result)
    return app(const("String.mk"), result)


def inventory(path, expand):
    names = {0: ("", h(["anonymous"]))}
    levels = {0: ZERO}
    exprs = {}
    decls = {}
    literals = []
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for raw in stream:
            digest.update(raw)
            row = json.loads(raw)
            if "in" in row:
                part = row.get("str", row.get("num"))
                prefix, prefix_h = names[part["pre"]]
                suffix = part.get("str", str(part.get("i")))
                names[row["in"]] = (prefix + ("." if prefix else "") + suffix,
                                     h(["name_str" if "str" in row else "name_num", prefix_h,
                                        part["str"] if "str" in row else part["i"]]))
            if "il" in row:
                if "succ" in row:
                    val = ["succ", levels[row["succ"]]]
                elif "param" in row:
                    val = ["param", names[row["param"]][1]]
                else:
                    key = "max" if "max" in row else "imax"
                    val = [key, *[levels[x] for x in row[key]]]
                levels[row["il"]] = h(val)
            if "ie" in row:
                key = next(key for key in row if key != "ie")
                val = row[key]
                if key == "strVal":
                    literals.append(val)
                    if not expand:
                        raise ValueError("Lowered export still contains a string literal")
                    exprs[row["ie"]] = lowered_literal(val)
                    continue
                if key in ("natVal", "bvar"):
                    term = [key, val]
                elif key == "sort":
                    term = [key, levels[val]]
                elif key == "const":
                    term = [key, names[val["name"]][1], [levels[x] for x in val["us"]]]
                elif key == "app":
                    term = [key, exprs[val["fn"]], exprs[val["arg"]]]
                elif key in ("lam", "forallE"):
                    term = [key, names[val["name"]][1], exprs[val["type"]],
                            exprs[val["body"]], val["binderInfo"]]
                elif key == "letE":
                    term = [key, names[val["name"]][1], exprs[val["type"]],
                            exprs[val["value"]], exprs[val["body"]], val["nondep"]]
                elif key == "proj":
                    term = [key, names[val["typeName"]][1], val["idx"], exprs[val["struct"]]]
                elif key == "mdata":
                    raise ValueError("Metadata expressions outside the reviewed export mode")
                else:
                    raise ValueError(f"Unknown expression record: {key}")
                exprs[row["ie"]] = h(term)
            groups = [(key, row[key]) for key in ("axiom", "def", "thm", "opaque", "quot") if key in row]
            if "inductive" in row:
                for field, kind in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    groups.extend((kind, item) for item in row["inductive"][field])
            for kind, item in groups:
                name = names[item["name"]][0]
                record = {"kind": kind, "type": exprs[item["type"]],
                          "level_parameters": [names[x][1] for x in item["levelParams"]]}
                if "value" in item:
                    record["value"] = exprs[item["value"]]
                if kind == "recursor":
                    record["rules"] = [(names[r["ctor"]][1], r["nfields"], exprs[r["rhs"]])
                                       for r in item["rules"]]
                if name in decls:
                    raise ValueError(f"Duplicate declaration {name}")
                decls[name] = record
    return {"sha256": digest.hexdigest(), "literals": literals, "declarations": decls,
            "expression_hashes": set(exprs.values())}


def main():
    before = inventory(PILOT / "exports-full/export.ndjson", True)
    after = inventory(PILOT / "exports-lowered/export.ndjson", False)
    prior = before["declarations"]
    current = after["declarations"]
    missing = sorted(set(prior) - set(current))
    extra = sorted(set(current) - set(prior))
    different = [name for name in prior.keys() & current.keys() if prior[name] != current[name]]
    expected = json.loads((ROOT / "literal-kernel-result.json").read_text())["actual_literals"]
    correct_literals = before["literals"] == [entry["value"] for entry in expected]
    passed = not missing and not extra and not different and correct_literals
    receipt = {
        "original_export_sha256": before["sha256"], "lowered_export_sha256": after["sha256"],
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "original_literal_count": len(before["literals"]), "lowered_literal_count": len(after["literals"]),
        "original_declaration_count": len(prior), "lowered_declaration_count": len(current),
        "missing_declarations": missing, "extra_declarations": extra,
        "different_declaration_types_or_values_or_recursor_rules": sorted(different),
        "literal_expansions_missing_from_lowered_dag": [text for text in before["literals"]
                                                       if lowered_literal(text) not in after["expression_hashes"]],
        "actual_literals_match_separate_kernel_checks": correct_literals,
        "numeric_representation": "Lean 4.19 mkNatLit = OfNat.ofNat Nat n (instOfNatNat n), as defined in Lean/Expr.lean:726",
        "all_structural_checks_passed": passed,
        "scope": "Declared types, proof/definition values, universes and recursor RHSs modulo only the reviewed string expansion; not an independent checker result",
    }
    (ROOT / "structural-comparison.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
