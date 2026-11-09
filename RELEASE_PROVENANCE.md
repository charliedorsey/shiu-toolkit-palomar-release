# Release verification and provenance

This file accompanies the standalone Shiu Bounds Toolkit source distribution.
It is reproducibility guidance, not a claim that the public registry has
accepted or indexed the work.

## Prepublication source candidate

The private engineering candidate was frozen at Git SHA:
`681e355148c4bd1ac656d45ed9de8598c4bdc4f9`.

On November 9, 2026 a GitHub-hosted Ubuntu court built this exact
candidate with Lean 4.35.0 and pinned Mathlib. It checked the full
proof library, Challenge and Solution, all 8 consumer examples, and the
3 advertised theorem axiom sets (`propext`, `Classical.choice`,
`Quot.sound`). The Palomar Comparator accepted the complete Solution,
con-ron accepted 45,799 exported declarations, and NanoDa and Lean's
default kernel both accepted the Solution. Independent AI mathematical
review was performed separately; no human journal peer review is claimed.

**Public release evidence:** the private verification court is not itself
evidence for a different Git tree. The corrected public source
commit `c49a08ac26c9efacdcc55d3c7a4cf2db03e0eca8` subsequently passed
the [official Palomar predictive preflight](https://github.com/charliedorsey/shiu-toolkit-palomar-release/actions/runs/42685020474)
and [Palomar closed-submission mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/42692549841)
on November 9, 2026. The associated automated editorial review reported
no blocking issues and one nonblocking fidelity-metadata disclosure
warning, addressed in the present metadata revision. The reviewer
report and public registration remain separate; this revision must be
verified under its own immutable commit.

## Reproducing the code checks

1. Install the Lean version named in `lean-toolchain`.
2. Fetch pinned dependencies using `lake exe cache get`.
3. Run `lake build ShiuToolkit Challenge Solution`.
4. Run `lake env lean` separately on every `examples/*.lean`.
5. For a trusted Linux machine with Lean's comparator tooling and
   Bubblewrap configured, run `bash scripts/verify-comparator.sh`.

The canonical `Challenge.lean` imports only Mathlib, with no
candidate-local modules. Its helper declarations are source-text mirrors
of the nine Mathlib-only `ChallengeDefs` modules used by the proved source.
Run `python3 scripts/check_canonical_challenge.py` to independently check
the mirrors. Because inlining into another Lean module can change
private elaboration witnesses, Comparator's four `definition_names`
targets match definition types but do not compare definition bodies.
That limitation must be distinguished from strict comparison of the
three theorem statements and from the separate source-text test.
The three `sorry` placeholders in Challenge are deliberate
contract holes, **not** holes in the proved library or Solution.

## Credits and scope

The source contains adapted Apache-2.0 code credited in source headers
and `NOTICE` to Arend Mellendijk, `selberg-sieve4`, and Mathlib.
The project is human-directed and AI-assisted; Charlie Dorsey was
the only human source-code contributor. See `formalization.yaml`,
`CITATION.cff`, and the theorem signatures for actual scope.
