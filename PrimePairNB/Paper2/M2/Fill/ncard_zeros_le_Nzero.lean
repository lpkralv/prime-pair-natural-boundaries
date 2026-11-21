import PrimePairNB.Paper2.M2.Fill.BCommon

/-! `ncard_zeros_le_Nzero` (`Single.lean`). The proof is `ncard_zeros_le_NzeroB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Distinct zeros versus `N(t)`** (unconditional). The zeros with `0 < γ ≤ t` are finitely many
(`finite_zeros_im_pos_le`, in `M1/Fill/sum_zetaMult_window_le.lean`), and their number is at most
`N(t) = ∑ m(ρ)` because `m(ρ) ≥ 1` (`one_le_zetaMult`; `Finset.card_eq_sum_ones`, `Finset.sum_le_sum`). For
`t ≤ 0` both sides are `0`. -/
theorem ncard_zeros_le_Nzero (t : ℝ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}.Finite ∧
      ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}.ncard : ℝ) ≤ Nzero t :=
  ncard_zeros_le_NzeroB t

end GoldbachBoundaries.Paper2.M2
