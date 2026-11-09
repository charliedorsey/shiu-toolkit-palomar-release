# Release verification and provenance

This file accompanies the standalone Shiu Toolkit source distribution.
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

**Important:** the successful court ran on a private repository. Its
log may not be accessible to readers of the public source. The public
repository needs its **own public build and Palomar predictive preflight**
for any definitive public verification claim. A different public commit
must not inherit the private source SHA's verification status by fiat.

## Reproducing the code checks

1. Install the Lean version named in `lean-toolchain`.
2. Fetch pinned dependencies using `lake exe cache get`.
3. Run `lake build ShiuToolkit Challenge Solution`.
4. Run `lake env lean` separately on every `examples/*.lean`.
5. For a trusted Linux machine with Lean's comparator tooling and
   Bubblewrap configured, run `bash scripts/verify-comparator.sh`.

The nine Mathlib-only `ChallengeDefs` modules are shared source-exact
definition dependencies for both the independent Challenge and proved
Solution. The three `sorry` placeholders in Challenge are deliberate
contract holes, **not** holes in the proved library or Solution.

## Credits and scope

The source contains adapted Apache-2.0 code credited in source headers
and `NOTICE` to Arend Mellendijk, `selberg-sieve4`, and Mathlib.
The project is human-directed and AI-assisted; Charlie Dorsey was
the only human source-code contributor. See `formalization.yaml`,
`CITATION.cff`, and the theorem signatures for actual scope.
