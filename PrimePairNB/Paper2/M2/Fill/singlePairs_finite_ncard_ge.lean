import PrimePairNB.Paper2.M2.Fill.BCommon

/-! `singlePairs_finite_ncard_ge` (`Single.lean`). The proof is `singlePairs_finite_ncard_geB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`|𝓟(X)| ≥ c₂ X²/log² X`** ((Z2), (Z5), the (Z4) witnesses). `singlePairs A₀ y ε X` is the disjoint union over
the zeros `ρ` of `ncard_lineZeros_window_geB` of `{ρ} × {q : γ/q ∈ J}` (`Set.Finite.biUnion`, and
`Set.ncard` of a disjoint finite union is the sum: via `Finset.card_sigma` or `Finset.card_biUnion`); each fibre has
at least `c₁ X/log² X` elements (`ncard_primes_window_geB`), and there are at least `A₀X/2` zeros. Take
`c₂ = A₀c₁/2`. -/
theorem singlePairs_finite_ncard_ge (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ᶠ X in atTop, (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) :=
  singlePairs_finite_ncard_geB hZ2 hZ5 hA₀ hN0 hy hε hεy

end GoldbachBoundaries.Paper2.M2
