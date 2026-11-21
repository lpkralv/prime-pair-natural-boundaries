import PrimePairNB.Paper2.M2.Defs

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

lemma A_finite_strip (t : ℝ) (L : ℕ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L}.Finite :=
  (finite_zeros_abs_im_le (|t| + L)).subset fun ρ ⟨hz, hl, hu⟩ =>
    ⟨hz, abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩

lemma A_ncard_le_weight {s : Set ℂ} (hs : s.Finite) (hz : s ⊆ NontrivialZeros) :
    (s.ncard : ℝ) ≤ wsumB s := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs, wsumB, finsum_mem_eq_finite_toFinset_sum _ hs]
  calc (hs.toFinset.card : ℝ) = ∑ _ ∈ hs.toFinset, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun ρ hρ => by
      exact_mod_cast one_le_zetaMult_of_zero (by
        have := (hz (hs.mem_toFinset.mp hρ)).2.2
        intro h; simp [h] at this) (hz (hs.mem_toFinset.mp hρ)).1

lemma A_log_scale {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N : ℝ) * x + N + 3) ≤
      (1 + Real.log (N + 1) / Real.log 3) * Real.log (x + 3) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlx : Real.log 3 ≤ Real.log (x + 3) := Real.log_le_log (by norm_num) (by linarith)
  have hlN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  calc Real.log ((N : ℝ) * x + N + 3)
      ≤ Real.log ((N + 1) * (x + 3)) := Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log (N + 1) + Real.log (x + 3) := Real.log_mul (by positivity) (by positivity)
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hlx (div_nonneg hlN hl3.le)
      have he : Real.log (N + 1) / Real.log 3 * Real.log 3 = Real.log (N + 1) :=
        div_mul_cancel₀ _ hl3.ne'
      nlinarith
end GoldbachBoundaries.Paper2.M2
