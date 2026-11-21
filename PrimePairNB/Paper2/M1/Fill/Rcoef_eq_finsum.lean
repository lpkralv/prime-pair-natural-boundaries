import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- For non-real `a ∈ Σ_Q`, `R_a` is the finite sum over the squarefree `k < 1/Re a` with `ka` a zero. -/
theorem Rcoef_eq_finsum {a : ℂ} (ha : a ∈ PoleSetQ) (him : a.im ≠ 0) :
    Rcoef a = -∑ᶠ k ∈ {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / a.re ∧
        (k : ℂ) * a ∈ NontrivialZeros}, mu k / k * (zetaMult ((k : ℂ) * a) : ℂ) := by
  classical
  have hpos := re_pos_of_mem_poleSetQ ha
  let S : Set ℕ := {k | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / a.re ∧
    (k : ℂ) * a ∈ NontrivialZeros}
  let f : ℕ → ℂ := fun k => mu k / k * (zetaMult ((k : ℂ) * a) : ℂ)
  have hterm : ∀ k : ℕ, mu k / k * (ordZeta ((k : ℂ) * a) : ℂ) = S.indicator f k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [S, f]
    have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hw1 : (k : ℂ) * a ≠ 1 := by
      intro heq
      have heq' := congrArg Complex.im heq
      simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, one_im] at heq'
      exact (mul_ne_zero hkR.ne' him) heq'
    by_cases hs : Squarefree k
    · by_cases hz : (k : ℂ) * a ∈ NontrivialZeros
      · have hlt : (k : ℝ) < 1 / a.re := by
          rw [lt_div_iff₀ hpos]
          simpa using hz.2.2
        have hmem : k ∈ S := ⟨by omega, hs, hlt, hz⟩
        simp [ordZeta, hw1, hz, Set.indicator_of_mem hmem, f]
      · have hmem : k ∉ S := fun h => hz h.2.2.2
        simp [ordZeta, hw1, hz, Set.indicator_of_notMem hmem]
    · have hmu : mu k = 0 := by
        by_contra hn
        exact hs (squarefree_of_mu_ne_zero hn)
      have hmem : k ∉ S := fun h => hs h.2.1
      simp [hmu, Set.indicator_of_notMem hmem]
  obtain ⟨M, _, hM⟩ := exists_tail_index hpos 1
  have hout : ∀ n, M ≤ n → 1 < ((n : ℂ) * a).re := by
    intro n hn
    have hnR : (M : ℝ) ≤ n := by exact_mod_cast hn
    simp only [re_natCast_mul]
    nlinarith
  have hsupp : Function.support (S.indicator f) ⊆ (Finset.range M : Set ℕ) := by
    intro k hk
    have hmem : k ∈ S := by
      by_contra hn
      exact hk (Set.indicator_of_notMem hn f)
    have hlt := hmem.2.2.2.2.2
    have hkM : k < M := by
      by_contra hn
      have hgt := hout k (by omega)
      linarith
    exact Finset.mem_range.mpr hkM
  rw [A_Rcoef_eq_sum M hout, finsum_mem_def,
    finsum_eq_finsetSum_of_support_subset (S.indicator f) hsupp]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => hterm k)

end GoldbachBoundaries.Paper2.M1
