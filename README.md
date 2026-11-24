# Lean formalization: natural boundaries of prime-pair Dirichlet series

Louis P. Slothouber

Lean 4 code for the paper

> Louis P. Slothouber, *Natural boundaries of prime-pair Dirichlet series*, preprint, Hexagon, hexagon:2611.00971, 2026.

This is release `v1.2.1`. Release `v1.2` added any-path non-extension theorems for G₂ and G_log, including paths that end at
catalogue points. Release `v1.1` introduced the results for these series in Theorem 1.3 and Section 9 of the paper.
License: Apache-2.0 (`LICENSE`).

## What it proves

The paper studies five Dirichlet series over ordered pairs of primes p, q:

* G(s) = Σ_{p,q} (p+q)^(-s), defined in Lean as `GoldbachBoundaries.G`;
* T(s) = Σ_{p,q} log p log q (p+q)^(-s), `GoldbachBoundaries.T`;
* S(s) = Σ_{p,q} p^(1-s) q^(2-s) / (p²+q²)², `GoldbachBoundaries.HInf.Sser` (the series `Dser WS`);
* G₂(s) = Σ_{p,q} (p²+q²)^(-s), `GoldbachBoundaries.HInf.SqSer` (the series `Dser WSq`);
* G_log(s) = Σ_{p,q} log q (p+q)^(-s), `GoldbachBoundaries.HInf.MixSer` (the series `Dser Wlogq`).

Under the hypothesis H∞ (for every δ > 0, only finitely many non-trivial zeros of ζ have real part greater than
1/2 + δ), the line Re s = 1 is a natural boundary of T, of G and of G_log, the line Re s = 1/2 is a natural boundary
of G₂, and the line Re s = 0 is a natural boundary of S. For G, S, G₂ and G_log the result holds on every branch
reached by analytic continuation along a path. The Riemann Hypothesis is not assumed. Section 10 of the paper
proves more under RH (Theorem 10.1). Lean checks that
theorem from RH alone, by a separate route that does not pass through the H∞ proof: `GoldbachBoundaries.thm_A`,
`GoldbachBoundaries.rem_every_path` and `GoldbachBoundaries.cor_T_poles`.

The main declarations are

| Paper | Lean |
|---|---|
| Theorem 1.1 (T) | `GoldbachBoundaries.Paper2.thm_boundary` |
| Theorem 1.2 (G and S) | `GoldbachBoundaries.HInf.boundary_G`, `GoldbachBoundaries.HInf.boundary_S`; conjunction `GoldbachBoundaries.HInf.boundary_GS`; admissible germs of S near the line: `GoldbachBoundaries.HInf.exists_admS_near`, `GoldbachBoundaries.HInf.exists_admS_iff` |
| Theorem 8.2 (paths) | `GoldbachBoundaries.HInf.every_path_stays_G`, `_S`, `GoldbachBoundaries.HInf.no_extension_any_path_G`, `_S`, `GoldbachBoundaries.HInf.cor_domain_G`, `_S` |
| Corollary 8.3 | `GoldbachBoundaries.HInf.every_path_G`, `GoldbachBoundaries.HInf.every_path_S`; conjunction `GoldbachBoundaries.HInf.every_path_GS` |
| Theorem 1.3 (G₂ and G_log) | (a) `GoldbachBoundaries.HInf.continuesAlong_Sq`, `_mix`, `GoldbachBoundaries.HInf.exists_admSq_iff`, `exists_admMix_iff`; admissible germs near the line: `GoldbachBoundaries.HInf.exists_admSq_near`, `exists_admMix_near`; (b) `GoldbachBoundaries.HInf.boundary_Sq`, `boundary_mix`; (c) `GoldbachBoundaries.HInf.every_path_Sq`, `every_path_mix` |
| Any-path non-extension for G₂ and G_log | `GoldbachBoundaries.HInf.no_extension_any_path_Sq`, `GoldbachBoundaries.HInf.no_extension_any_path_mix` |
| Theorem 10.1 (under RH) | `GoldbachBoundaries.thm_A`, `GoldbachBoundaries.rem_every_path`, `GoldbachBoundaries.cor_T_poles` |

`CORRESPONDENCE.md` maps every numbered result of the paper to its Lean declarations, with their exact hypotheses
and the points where the Lean statement differs in form from the printed one. Appendix A of the paper reproduces
the main statements and the definitions they use, verbatim with docstrings and proofs omitted.

`GoldbachBoundaries.HInf.exists_admG` and `GoldbachBoundaries.HInf.exists_admS` show that the admissibility
hypotheses `AdmG` and `AdmS` of the G and S theorems are not vacuous: G is an admissible germ at 3, and S at 2.
The boundary statements also need admissible germs close to the line, in every disc about one of its points. For S
this is `GoldbachBoundaries.HInf.exists_admS_near`: under H∞ and Z1 to Z3, every disc about a point of Re s = 0
contains a point that carries an admissible germ of S. More precisely, `GoldbachBoundaries.HInf.exists_admS_iff`
says that a point carries one exactly when it lies in Re s > 0 and off the catalogue of S. Together with
`GoldbachBoundaries.HInf.boundary_S` this gives the natural boundary of S at Re s = 0 on every branch. For G the
germs near Re s = 1 come from `GoldbachBoundaries.HInf.continuesAlong_G`. For G₂ and G_log,
`exists_admSq_near` and `exists_admMix_near` give admissible germs in every disc about a point of Re s = 1/2 and
Re s = 1 respectively, under H∞, Z1 to Z3 and Z6; `exists_admSq_iff` and `exists_admMix_iff` say exactly which
points carry one.

## Companion documents

The author wrote these with AI assistance while the paper was being developed, so that he could follow and check every step. Other readers may find them useful.

- [Summary](companions/SUMMARY.pdf): what the paper proves, why it matters, and how it was found and checked.
- [Reading guide](companions/READING-GUIDE.pdf): a section-by-section companion that writes out the steps the paper skips.
- [Primer](companions/PRIMER.pdf): the background the paper assumes, written for a reader with a computer-science background and some complex analysis. It is also a record of how the author learned the material.

Markdown sources are in the same folder. The paper is the authority; if a companion and the paper disagree, the paper is right.

## Hypotheses

The theorems are implications. Their hypotheses are H∞ and six classical facts, Z1 to Z6. Each is a Lean `Prop`
about Mathlib's `riemannZeta` and `Complex.Gamma`, defined in `PrimePairNB/Paper2/Defs.lean` in the namespace
`GoldbachBoundaries.Paper2`, and taken as an explicit argument of the theorems that use it. None is an `axiom` and
none is proved here. What Lean checks is that the hypotheses imply the theorems.

| Name | Lean | Statement |
|---|---|---|
| H∞ | `Hinf` | for every δ > 0, the set of non-trivial zeros ρ with Re ρ > 1/2 + δ is finite |
| Z1 | `Z1` | if ρ is a non-trivial zero, so are conj ρ and 1 − conj ρ, with the same multiplicity |
| Z2 | `Z2` | Riemann–von Mangoldt: N(t) = (t/2π) log(t/2π) − t/2π + O(log t), and N(t+1) − N(t) ≤ C₁ log(t+3) for t ≥ 0 (N counts with multiplicity) |
| Z3 | `Z3` | for −1 ≤ Re z ≤ 2, \|Im z\| ≥ 2, ζ(z) ≠ 0: ζ′/ζ(z) minus the sum of m(ρ)/(z−ρ) over zeros with \|Im ρ − Im z\| ≤ 1 is O(log \|Im z\|) |
| Z4 | `Z4` | Hardy–Littlewood: the number N₀(t) of distinct zeros 1/2 + iγ with 0 < γ ≤ t satisfies N₀(t) ≥ A₀t for t ≥ t₀, some A₀ > 0 |
| Z5 | `Z5` | for each θ > 0 and all large x, the open interval (x, (1+θ)x) contains at least θx/(2 log x) primes |
| Z6 | `Z6` | for 0 < x₁ ≤ x₂ there is C with \|Γ(x+iy)\| ≤ C(1+\|y\|)^x₂ e^(−π\|y\|/2) for x₁ ≤ x ≤ x₂ and all real y |

Z1 to Z6 are classical theorems (Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Chapters II, IX
and X; the prime number theorem; Stirling's formula). The paper gives the sources in Section 2; the passage from
the textbook statements to these Lean forms is checked by hand there, not in Lean. H∞ is the paper's hypothesis.
The Riemann Hypothesis implies it. The Lean statements of Theorem 10.1 take Mathlib's `RiemannHypothesis` as
their only hypothesis.

## Layout

The library has 361 Lean files (39,337 lines): the root `PrimePairNB.lean` and 360 files under `PrimePairNB/`
(128 in `Paper2/`, 141 in `HInf/`, 63 in `ThmA/`, 17 in `TIdentity/`, the rest at the top level).
`CheckAxioms.lean` is not counted.
Its declarations live in the namespace `GoldbachBoundaries` and its sub-namespaces `Paper2`, `HInf`, `ThmA` and
`TIdentity`, kept from the larger development the library was extracted from; the directory layout follows that
development's modules. The library holds the declarations that the cited theorems use, transitively, and nothing
else.
The library requires PrimeNumberTheoremAnd directly and uses Mathlib through it; `lake-manifest.json` pins these two
and the further packages they depend on, 14 packages in all.

## Versions

* 1.2.1: CORRESPONDENCE.md updated for the two v1.2 declarations; no Lean change.

* Lean 4.34.0 (`lean-toolchain`)
* Mathlib, tag v4.34.0
* PrimeNumberTheoremAnd, commit c39a751 (c39a751132c88b6e8080b74c74023fd95b3d8be0)

`lake-manifest.json` pins every dependency to an exact commit.

## Build and check

With elan installed (it reads `lean-toolchain` and fetches the right Lean), from this folder:

    lake exe cache get              # downloads the Mathlib build cache
    lake build                      # builds PrimeNumberTheoremAnd and PrimePairNB
    lake env lean CheckAxioms.lean  # prints the axioms of every cited theorem

`lake build` should end with `Build completed successfully`. `CheckAxioms.lean` runs `#print axioms` on each of
the 74 theorems listed in it; every line should read

    'GoldbachBoundaries.Paper2.thm_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]

with the declaration's name. These are the three standard axioms of Lean's logic; no `sorry` and no other axiom
is used. The library contains no `sorry`, `admit`, `native_decide` or `axiom` declaration.

The v1.2 clean build used the unpacked Mathlib cache on macOS (Apple silicon) with the pinned Lean 4.34.0.
It rebuilt PrimeNumberTheoremAnd and this library in about 95 minutes and ended with
`Build completed successfully (9370 jobs).` All 74 lines of `CheckAxioms.lean` listed only `propext`,
`Classical.choice` and `Quot.sound`.

The build prints warnings. Those in `PrimePairNB` are linter and deprecation notices. Two are
`declaration uses 'sorry'` in PrimeNumberTheoremAnd's own `Wiener.lean`; nothing in this library depends on them,
as the axiom check shows (a dependence on `sorry` would add `sorryAx` to the list).

## License

Apache License 2.0; see `LICENSE`.
