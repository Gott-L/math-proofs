"""Verify only this supplement's explicit file whitelist and SHA-256 hashes.

No proof execution, dependency installation, or network access is performed.
"""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text("utf-8"))
expected = set(manifest["files"]) | {"MANIFEST.json"}
actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
if expected != actual:
    raise SystemExit(f"Whitelist mismatch: missing={expected-actual}; extra={actual-expected}")
for name, item in manifest["files"].items():
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()):
        raise SystemExit("Manifest path escapes package")
    data = path.read_bytes()
    if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
        raise SystemExit("Hash mismatch: " + name)
print(f"Verified {len(expected)} whitelisted files; no proof or checker was executed.")
