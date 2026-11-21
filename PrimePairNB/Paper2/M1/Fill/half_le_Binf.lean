import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

/-! `half_le_Binf` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `1/2 ≤ B_∞` (Z1): for every `t` there is a zero with `|γ| ≥ t`, and of `ρ`, `1 - ρ̄` (same `|γ|`) one has
`β ≥ 1/2`; so every `sSup` in the family is `≥ 1/2`. -/
theorem half_le_Binf (hZ1 : Z1) : 1 / 2 ≤ Binf := by
  rw [Binf_eq_iInf]
  refine le_ciInf fun t => ?_
  obtain ⟨ρ, hρ, h⟩ := exists_nontrivialZero_im_gt |t|
  have ht : t ≤ |ρ.im| := (le_abs_self t).trans (h.le.trans (le_abs_self _))
  have h1 := (hZ1 ρ hρ).2.1
  have ht' : t ≤ |(1 - conj ρ).im| := by simpa using ht
  rcases le_total (1 / 2) ρ.re with hr | hr
  · exact hr.trans (re_le_binfFam hρ ht)
  · refine le_trans ?_ (re_le_binfFam h1 ht')
    simp only [sub_re, one_re, conj_re]
    linarith

/-! Consequences of this file's lemma. -/

/-- Points of `Σ_Q` have real part at most `1 ≤ 2B_∞` (Z1). -/
lemma halfPlane_two_Binf_subset (hZ1 : Z1) {a : ℂ} (ha : a ∈ PoleSetQ) :
    halfPlane (2 * Binf) ⊆ halfPlane a.re := by
  intro s hs
  have h1 := (poleSetQ_re_bounds ha).2.1
  have h2 := half_le_Binf hZ1
  have h3 : 2 * Binf < s.re := hs
  show a.re < s.re
  linarith

end GoldbachBoundaries.Paper2.M1
