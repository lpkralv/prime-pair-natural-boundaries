import PrimePairNB.Paper2.M1.QnoRH

/-!
# The numbers `B` and `B_∞`

`Bsup = sSup (re '' Z)` and `Binf = ⨅ t, sSup (re '' {ρ ∈ Z : t ≤ |γ|})` (`Paper2/Defs.lean`). Each set is non-empty
(zeros of every height: `exists_nontrivialZero_im_gt`, `exists_nontrivialZero_im_lt` in `Density.lean`) and bounded
above by `1`, so the suprema are genuine; the infimum is over a family bounded below by `0`. The lemmas about these
numbers (`half_le_Binf`, `Binf_le_Bsup_le_one`, `finite_zeros_re_gt`, `Fdelta_spec`, `Bsup_lt_one_of_Hinf`,
`exists_goodHeight`) are proved in `Fill/<name>.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `B_∞ < 1` follows from an admissible `(δ, c)`. -/
lemma AdmC.Binf_lt_one {δ c : ℝ} (h : AdmC δ c) : Binf < 1 := by
  obtain ⟨hδ, hδ1, -⟩ := h
  linarith

end GoldbachBoundaries.Paper2.M1
