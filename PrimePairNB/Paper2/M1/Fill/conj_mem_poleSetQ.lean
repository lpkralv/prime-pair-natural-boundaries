import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Σ_Q` is closed under conjugation (`conj_mem_nontrivialZeros`, `conj (ρ/n) = conj ρ / n`). -/
theorem conj_mem_poleSetQ {a : ℂ} (ha : a ∈ PoleSetQ) : conj a ∈ PoleSetQ := by
  rcases ha with (ha | ⟨k, hk, hs, rfl⟩) | ⟨n, hn, hs, ρ, hρ, rfl⟩
  · simpa [mem_singleton_iff.mp ha] using (show (1 : ℂ) ∈ PoleSetQ from Or.inl (Or.inl rfl))
  · exact Or.inl (Or.inr ⟨k, hk, hs, by simp⟩)
  · exact Or.inr ⟨n, hn, hs, conj ρ, conj_mem_nontrivialZeros hρ, by simp⟩

/-! Consequences of this file's lemma. -/

/-- `Π` is closed under conjugation. -/
lemma conj_mem_Pinch {s : ℂ} (hs : s ∈ Pinch) : conj s ∈ Pinch := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact ⟨conj a, conj_mem_poleSetQ ha, conj b, conj_mem_poleSetQ hb, map_add _ a b⟩

end GoldbachBoundaries.Paper2.M1
