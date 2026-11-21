import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon

/-! `finite_zeros_re_gt` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- For `δ > 0` only finitely many zeros have `β > B_∞ + δ` (no hypothesis): some `t` has
`sSup {β : |γ| ≥ t} < B_∞ + δ` (`ciInf_lt_iff`), and the zeros with `|γ| < t`, `β > B_∞ + δ > 0` lie in a compact
set; zeros of `ζ` in a compact set are finite (`riemannZeta_zeros_finite_of_isCompact`, or Mathlib's
`IsCompact.inter_riemannZetaZeros_finite`). -/
theorem finite_zeros_re_gt (δ : ℝ) (hδ : 0 < δ) :
    {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  obtain ⟨t, ht⟩ := exists_binfFam_lt hδ
  refine (finite_zeros_abs_im_le t).subset ?_
  rintro ρ ⟨hρ, hre⟩
  refine ⟨hρ, ?_⟩
  by_contra h
  push Not at h
  have := re_le_binfFam hρ h.le
  linarith

end GoldbachBoundaries.Paper2.M1
