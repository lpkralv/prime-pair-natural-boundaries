import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The supremum `B` (Z1): every zero has `β ≤ B`, `1/2 ≤ B ≤ 1`. The set `re '' Z` is non-empty (zeros exist,
`exists_nontrivialZero_im_gt` in `Density.lean`) and bounded by `1`; (Z1) gives a zero `1 - ρ̄` with
`β ≥ 1/2`. -/
theorem Bsup_facts (hZ1 : Z1) :
    (∀ ρ ∈ NontrivialZeros, ρ.re ≤ Bsup) ∧ 1 / 2 ≤ Bsup ∧ Bsup ≤ 1 := by
  have hb : BddAbove (re '' NontrivialZeros) := ⟨1, by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.2.2.le⟩
  have hle : ∀ ρ ∈ NontrivialZeros, ρ.re ≤ Bsup := fun ρ hρ => le_csSup hb ⟨ρ, hρ, rfl⟩
  obtain ⟨ρ, hρ, _⟩ := exists_nontrivialZero_im_gt 0
  refine ⟨hle, ?_, csSup_le ⟨ρ.re, ρ, hρ, rfl⟩ (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2.le)⟩
  have h₁ := hle ρ hρ
  have h₂ := hle (1 - conj ρ) (hZ1 ρ hρ).2.1
  simp only [sub_re, one_re, conj_re] at h₂
  linarith

end GoldbachBoundaries.Paper2.M1
