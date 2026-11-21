import PrimePairNB.BoundaryLemma
import PrimePairNB.TIdentity.Assembly

/-!
# The natural boundary of `T`, taking the density lemma as a hypothesis

Under RH, the line `σ = 1` is a natural boundary of `T`. The proof
here takes the density statement (for every `y` and `ε > 0` there are infinitely many pairs
`(p, ρ)`, `p` prime, `ρ` a non-trivial zero, with `|ρ/p - iy| < ε`) as the hypothesis `hdens`.

Route:
1. `cor_T_poles_proof` gives a continuation `F₀` of `T`, meromorphic on `ℍ`, with a simple pole
   (order `-1`) at every catalogue point. Any `F` meromorphic on `ℍ` and equal to `T` off a
   discrete subset of `σ > 2` agrees with `F₀` on a punctured neighbourhood of every point of `ℍ`
   (`F - F₀` has order `⊤` at `3`, hence at every point of the connected set `ℍ`), so it has the
   same orders there (`meromorphicOrderAt_eq_of_eqOn_halfPlane_two`).
2. For `z₀ = 1 + iy` and `ε > 0`, `hdens` gives a prime `p` and a non-trivial zero `ρ` with
   `|ρ/p - iy| < ε`; then `a = 1 + ρ/p` is a catalogue point (primes are squarefree), lies in `ℍ`
   (`Re ρ > 0`), differs from `z₀` (`Re a > 1`), and lies in `Δ(z₀, ε)`.
3. `noMeromorphicExtensionAt_of_poles_in_every_ball` with `U = ℍ`.

RH enters only through `cor_T_poles_proof`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- The half-plane `{Re s > a}` is preconnected (it is convex). -/
lemma isPreconnected_halfPlane (a : ℝ) : IsPreconnected (halfPlane a) :=
  (convex_halfSpace_re_gt a).isPreconnected

end GoldbachBoundaries
