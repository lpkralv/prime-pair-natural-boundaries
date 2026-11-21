import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon

/-! `Binf_le_Bsup_le_one` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `B_∞ ≤ B ≤ 1` (no hypothesis): each `sSup` of the family is at most `B` (subset) and `B ≤ 1`. -/
theorem Binf_le_Bsup_le_one : Binf ≤ Bsup ∧ Bsup ≤ 1 := by
  refine ⟨(Binf_le_binfFam 0).trans ?_, ?_⟩
  · show sSup _ ≤ sSup _
    exact csSup_le_csSup (re_image_bddAbove subset_rfl) (re_image_nonempty_height 0)
      (image_mono fun ρ h => h.1)
  · obtain ⟨ρ, hρ⟩ := nontrivialZeros_nonempty
    exact csSup_le ⟨ρ.re, ρ, hρ, rfl⟩ (by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.2.2.le)

end GoldbachBoundaries.Paper2.M1
