import PrimePairNB.Paper2.M2.Defs
import PrimePairNB.Paper2.M2.Fill.zetaMult_le_log
import PrimePairNB.Paper2.M2.Fill.ACommon
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`|R_a| ≪_ε log(|Im a| + 3)`** on `Re a ≥ ε` (Z1, Z2; first half of Paper, Lemma 2.1). A real point of `Σ_Q` is
`1` or `1/k` (a point `ρ/n` is not real, since no zero in the strip is real: the RH development's
`riemannZeta_ne_zero_of_mem_Ioo`), so `|R_a| ≤ 1` (`Rcoef_one'`, `Rcoef_inv`, `|μ(k)| ≤ 1`). For non-real `a`,
`Rcoef_eq_finsum`: the index set has `k < 1/Re a ≤ 1/ε`, and each term is `≤ m(ka) ≤ C₀ log(k|Im a| + 3)`
(`zetaMult_le_log`, `Im(ka) = k Im a`) `≤ C₀ (log(1/ε + 1) + log(|Im a| + 3))`. Use `log(|Im a| + 3) ≥ log 3 > 0` to
absorb constants. -/
theorem norm_Rcoef_le_log (hZ1 : Z1) (hZ2 : Z2) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, ∀ a ∈ PoleSetQ, ε ≤ a.re → ‖Rcoef a‖ ≤ C * Real.log (|a.im| + 3) := by
  classical
  obtain ⟨N, hN1, hN⟩ := exists_tail_index hε 1
  obtain ⟨C₀, hC₀⟩ := zetaMult_le_log hZ1 hZ2
  let D := max C₀ 0
  let E := 1 + Real.log (N + 1) / Real.log 3
  let B := 1 / Real.log 3 + D * E
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := le_max_right _ _
  have hlN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨N * B, fun a ha hεa => ?_⟩
  have hl : Real.log 3 ≤ Real.log (|a.im| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg a.im])
  have hl0 : 0 ≤ Real.log (|a.im| + 3) := hl3.le.trans hl
  have hunit : 1 ≤ B * Real.log (|a.im| + 3) := by
    have h := mul_le_mul_of_nonneg_left hl (le_of_lt (one_div_pos.mpr hl3))
    have he : 1 / Real.log 3 * Real.log 3 = 1 := one_div_mul_cancel hl3.ne'
    dsimp [B]
    nlinarith [mul_nonneg (mul_nonneg hD hE) hl0]
  have hout : ∀ n, N ≤ n → 1 < ((n : ℂ) * a).re := by
    intro n hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    simp only [re_natCast_mul]
    nlinarith
  rw [A_Rcoef_eq_sum N hout, norm_neg]
  calc ‖∑ n ∈ Finset.range N, mu n / n * (ordZeta ((n : ℂ) * a) : ℂ)‖
      ≤ ∑ n ∈ Finset.range N, ‖mu n / n * (ordZeta ((n : ℂ) * a) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Finset.range N, B * Real.log (|a.im| + 3) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · simp only [hn0, Nat.cast_zero, div_zero, zero_mul, norm_zero]
        positivity
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
      have hmu : ‖mu n / (n : ℂ)‖ ≤ 1 := by
        rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity : (0 : ℝ) < n)]
        linarith [norm_mu_le_one n]
      have hord : ‖(ordZeta ((n : ℂ) * a) : ℂ)‖ ≤ B * Real.log (|a.im| + 3) := by
        by_cases hw : (n : ℂ) * a = 1
        · simpa [ordZeta, hw] using hunit
        by_cases hz : (n : ℂ) * a ∈ NontrivialZeros
        · simp only [ordZeta, if_neg hw, if_pos hz, Int.cast_natCast, Complex.norm_natCast]
          have hzero := hC₀ _ hz
          have hlog0 : 0 ≤ Real.log (|((n : ℂ) * a).im| + 3) := Real.log_nonneg (by linarith [abs_nonneg (((n : ℂ) * a).im)])
          have hscale : Real.log (|((n : ℂ) * a).im| + 3) ≤ E * Real.log (|a.im| + 3) := by
            calc _ ≤ Real.log ((N : ℝ) * |a.im| + N + 3) := by
                  apply Real.log_le_log (by positivity)
                  simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
                  nlinarith [abs_nonneg a.im]
              _ ≤ _ := A_log_scale (abs_nonneg _) hN1
          calc _ ≤ C₀ * Real.log (|((n : ℂ) * a).im| + 3) := hzero
            _ ≤ D * Real.log (|((n : ℂ) * a).im| + 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
            _ ≤ D * (E * Real.log (|a.im| + 3)) := mul_le_mul_of_nonneg_left hscale hD
            _ ≤ _ := by dsimp [B]; nlinarith [mul_nonneg (le_of_lt (one_div_pos.mpr hl3)) hl0]
        · simp [ordZeta, hw, hz, mul_nonneg hB hl0]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hmu (norm_nonneg _)).trans (by simpa using hord)
    _ = _ := by simp; ring
end GoldbachBoundaries.Paper2.M2
