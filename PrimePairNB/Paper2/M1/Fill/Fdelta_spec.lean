import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.finite_zeros_re_gt
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
/-! `Fdelta_spec` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `F_δ` (Z1): finite, and for `δ < 1 - B_∞` equal to `{1} ∪ {ρ : β > B_∞ + δ}` (the other points of `Σ_Q` have
real part `≤ 1/2 ≤ B_∞`, `poleSetQ_re_bounds`, `half_le_Binf`). Uses: `finite_zeros_re_gt`, `half_le_Binf`,
`poleSetQ_re_bounds`. -/
theorem Fdelta_spec (hZ1 : Z1) (δ : ℝ) (hδ : 0 < δ) :
    (Fdelta δ).Finite ∧
      (δ < 1 - Binf → Fdelta δ = {1} ∪ {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}) := by
  have hB := half_le_Binf hZ1
  have hsub : Fdelta δ ⊆ {1} ∪ {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re} := by
    rintro a ⟨ha, hre⟩
    rcases ha with (h1 | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
    · exact Or.inl h1
    · exfalso
      rw [re_one_div_natCast] at hre
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
      linarith
    · rcases eq_or_lt_of_le hn with h | h
      · subst h
        right
        simp only [Nat.cast_one, div_one] at hre ⊢
        exact ⟨hρ, hre⟩
      · exfalso
        rw [Complex.div_natCast_re] at hre
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h
        have : ρ.re / n ≤ 1 / 2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [hρ.2.2]
        linarith
  refine ⟨((finite_singleton 1).union (finite_zeros_re_gt δ hδ)).subset hsub, fun hδ1 => ?_⟩
  refine hsub.antisymm ?_
  rintro a (h | ⟨hρ, hre⟩)
  · rw [mem_singleton_iff.mp h]
    exact ⟨Or.inl (Or.inl rfl), by simp only [one_re]; linarith⟩
  · exact ⟨Or.inr ⟨1, le_rfl, squarefree_one, a, hρ, by simp⟩, hre⟩

end GoldbachBoundaries.Paper2.M1
