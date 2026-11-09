# Shiu Bounds Toolkit

A Lean 4 formalization of a fixed-quarter Brun–Titchmarsh-type bound
for nonnegative multiplicative arithmetic functions, with importable
corollaries for individual classical weights, wider interval exponents,
ordinary short intervals at modulus one, and a restricted two-parameter
region.

**License:** Apache-2.0, with preserved third-party notices in
[NOTICE](NOTICE). This README documents the publicly available proof
source. Making a source repository public is separate from publicly
registering its formalization with Palomar.

## The mathematical results

The main theorem, `Shiu.API.classical_quarter`, is a uniform
fixed-quarter specialization of the estimate in P. M. Shiu (1980).
For fixed A and B it chooses a threshold X0 **before the weight f**,
with a nonnegative, multiplicative classical weight satisfying the
prime-power envelope and the additional uniform growth witness
f(n) <= B n^(1/1280) for all positive n. Under the reduced progression
conditions 0<a<k, gcd(a,k)=1,
x^(1/4)<y<=x, and k<y^(3/4), it supplies the classical bound with
the proven constant `Shiu.API.classicalConstant A B` and
`exp(Shiu.API.primeMass f x k)`.

The theorem `Shiu.API.classical_modulus_one_quarter` proves the
ordinary short-interval case k=1 as a **derived** result. Its bound uses
exactly nine times the existing classical constant. It does not impose
squarefree support.

The theorem `Shiu.API.classical_two_parameter_quadrant` covers
1/4<=alpha,beta<1/2. The threshold is chosen once before alpha,
beta and f for fixed A,B, while the ranges are x^beta<y<=x
and k<y^(1-alpha). This extends the *interface* by monotonicity,
not by a new analytic estimate.

The separate squarefree-supported family has different hypotheses
and is not an extension of the non-squarefree classical result.

## What it does not prove

Shiu's full historical range 0<alpha,beta<1/2 is **not** formalized.
Neither parameter is allowed below 1/4 in the two-parameter theorem.
The main API uses natural endpoints x,y and retains the independent
fixed-B growth condition; it must not be advertised as the full
original function-class uniformity. The older Theorems 2–5 of the
original thesis, and new zeta applications, are not claimed.

Constants are explicit but extremely large. These are asymptotic
theorems with formal threshold conditions, not numerical optimization
routines.

## Lean imports

With a compatible Lean 4.35.0 and pinned Mathlib, import the
specific result rather than pulling in the whole library:

```lean
import Shiu.Classical
import Shiu.ModulusOneFinal
import Shiu.TwoParameter
```

The aggregate `import Shiu` exposes these and the other supported
API families. See the eight checked-in examples in `examples/` and
the source signatures for all hypotheses.

## Verification and provenance

The proof sources use Lean 4.35.0 with pinned Mathlib (see
`lean-toolchain` and `lake-manifest.json`). For a clean checkout:

```sh
lake exe cache get
lake build ShiuToolkit Challenge Solution
for f in examples/*.lean; do lake env lean "$f"; done
```

The three advertised theorems are defined and proved in the library;
the independent `Challenge.lean` contains their exact statements with
three **deliberate placeholders**, as required by the Comparator format.
`Challenge.lean` imports **only Mathlib**, so the official Palomar
canonical Challenge compiler does not need to trust any project-local
imports. It mirrors the shared definitions from nine audited
`ChallengeDefs/` source modules, which remain imported by the proved
source. Run `python3 scripts/check_canonical_challenge.py` to check
the copied source text against those modules.

To accommodate different module-local elaboration witnesses,
`comparator.json` also names four elaboration-sensitive helper definitions as
*definition targets*. Comparator checks their types but deliberately
does **not** check their bodies for identity. The source-text mirror
test is an additional integrity check, not a substitute for a
kernel-certified equivalence of independently elaborated definitions.
The three advertised theorem statements are still strict Comparator
theorem targets. The proved source and Solution have **zero unresolved `sorry`**;
the three Challenge placeholders do not count as proof claims.

The source candidate corresponding to private development commit
`681e355148c4bd1ac656d45ed9de8598c4bdc4f9` passed an independent
Ubuntu source build, all eight consumer examples and principal axiom
audits, and the real Palomar Comparator using NanoDa, con-ron and Lean's
default kernel on November 9, 2026. These private prepublication checks
are **not** a substitute for an official replay of a public commit.
The original public source commit
`c49a08ac26c9efacdcc55d3c7a4cf2db03e0eca8` subsequently passed
the [official predictive preflight](https://github.com/charliedorsey/shiu-toolkit-palomar-release/actions/runs/42685020474)
and the [Palomar registry-side mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/42692549841)
on November 9, 2026. Its private AI editorial review found no blocking
problem but identified a nonblocking disclosure gap, addressed in this
metadata revision. Neither the original checks nor the review automatically
certify a later commit. See [RELEASE_PROVENANCE.md](RELEASE_PROVENANCE.md)
for the verification boundary.

For a trusted Linux environment with the Palomar Comparator toolchain
installed and Bubblewrap enabled, run:

```sh
bash scripts/verify-comparator.sh
```

The main theorems depend only on the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.
An independent **AI** mathematical reviewer audited the scope and
source-facing proofs; this was *not* human journal peer review.

## Mathematical and bibliographic origins

P. M. Shiu, “A Brun–Titchmarsh theorem for multiplicative functions,”
*Journal für die reine und angewandte Mathematik* **313** (1980),
161–170. See also Shiu's 1980 Nottingham thesis,
*Studies in Multiplicative Number Theory*, chapter 3
([archive link](https://eprints.nottingham.ac.uk/28304/1/281269.pdf)).

Four Selberg-sieve modules adapt Apache-2.0 code from
Arend Mellendijk's `selberg-sieve4` development and Mathlib's
`SelbergSieve.lean`. Their source headers and
[NOTICE](NOTICE) preserve the relevant credits and modification notices.
No scanned thesis pages are included.

## Project authorship

Charlie Dorsey is the human project director and sole human source-code
contributor. AI systems substantially assisted with Lean proof
development, source adaptations, testing, review, and documentation.
The bibliographic author field records human responsibility, not a
claim of exclusive copyright in autonomous machine-generated text.

This source repository and its verification runs are not a public Palomar
registry entry or journal publication. Registration and publication require
separate, explicit approval by the responsible maintainer.
