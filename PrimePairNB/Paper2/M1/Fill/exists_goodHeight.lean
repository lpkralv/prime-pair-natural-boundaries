import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.finite_zeros_re_gt
/-! `exists_goodHeight` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- For `δ > 0` there is a height `H` as in Paper, Lemma 2.2 (`H ≥ 2`, every zero with `|γ| ≥ H - 1` has
`β ≤ B_∞ + δ`): take `H` above the finitely many exceptions. Uses: `finite_zeros_re_gt`. -/
theorem exists_goodHeight (δ : ℝ) (hδ : 0 < δ) : ∃ H : ℝ, GoodHeight δ H := by
  obtain ⟨M, hM⟩ := ((finite_zeros_re_gt δ hδ).image fun ρ => |ρ.im|).bddAbove
  refine ⟨max 2 (M + 2), le_max_left _ _, fun ρ hρ hH => ?_⟩
  by_contra hr
  push Not at hr
  have h1 : |ρ.im| ≤ M := hM ⟨ρ, ⟨hρ, hr⟩, rfl⟩
  have h2 := le_max_right 2 (M + 2)
  linarith

end GoldbachBoundaries.Paper2.M1
