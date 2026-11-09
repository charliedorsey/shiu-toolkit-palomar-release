#!/usr/bin/env python3
"""Check that Palomar's self-contained Challenge mirrors all shared source definitions.

This is a SOURCE-TEXT fidelity guard, not a replacement for Palomar's kernel
and declaration-identity comparison.
"""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
challenge = (root / "Challenge.lean").read_text()
assert challenge.startswith("module\n\npublic import Mathlib\n\npublic section\n")
assert re.findall(r"(?m)^public import (.+)$", challenge) == ["Mathlib"]
names = ["Envelope", "Cutoff", "SmallPrime", "Rankin", "ClassI",
         "ClassIV", "Mass", "Progressions", "Constant"]
for name in names:
    body = (root / "ChallengeDefs" / (name + ".lean")).read_text()
    assert body.count("public section\n") == 1, name
    section = body.split("public section\n", 1)[1].strip()
    assert challenge.count(section) == 1, f"shared source does not match: {name}"
config = json.loads((root / "comparator.json").read_text())
assert config["challenge_module"] == "Challenge"
assert config["solution_module"] == "Solution"
assert config["theorem_names"] == [
    "Shiu.API.classical_quarter",
    "Shiu.API.classical_modulus_one_quarter",
    "Shiu.API.classical_two_parameter_quadrant"
]
assert config["definition_names"] == [
    "Shiu.smallPrimeConstant",
    "PaperB.M4B.classicalClassIVRankinH",
    "PaperB.M4B.corvethClassicalClassIConstant",
    "PaperB.M4B.classicalShiuClassIVConstant"
]
assert len(re.findall(r"(?m)^  sorry$", challenge)) == 3
print("CANONICAL_CHALLENGE_SOURCE_FIDELITY_PASS", len(names), "shared exact text modules")
