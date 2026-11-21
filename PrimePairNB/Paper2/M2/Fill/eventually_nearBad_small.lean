import PrimePairNB.Paper2.M2.Far

/-! `eventually_nearBad_small` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Good pairs beat near-bad ones** (real analysis). With `L = log X ≥ max(1, Y + 3)` the bracket is at most
`9CL²`, so the left side is at most `(|N| + 81C²)L⁴`, and `L⁶ = o(X²)` (`isLittleO_log_rpow_rpow_atTop`). -/
theorem eventually_nearBad_small {c C Y : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hY : 0 ≤ Y) (N : ℝ) :
    ∀ᶠ X in atTop, N + (C * (2 * Real.log X + Y + 1) * Real.log (2 * Real.log X + Y + 3)) ^ 2 ≤
      c / 2 * X ^ 2 / Real.log X ^ 2 := by
  set K : ℝ := |N| + 81 * C ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) (two_pos : (0 : ℝ) < 2)).bound
    (show 0 < c / (2 * (K + 1)) by positivity)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (Y + 3))
  filter_upwards [hlo, hlog, eventually_gt_atTop (0 : ℝ)] with X hX hL hX0
  set L := Real.log X with hLdef
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLY : Y + 3 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  -- the bracket
  have hlog3 : Real.log (2 * L + Y + 3) ≤ 3 * L := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * L + Y + 3 by linarith)
    have h2 : Real.log (2 * L + Y + 3) ≤ Real.log (3 * L) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 3 * L by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (2 * L + Y + 3) := Real.log_nonneg (by linarith)
  have hbr0 : 0 ≤ C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3) := by
    have : 0 ≤ 2 * L + Y + 1 := by linarith
    positivity
  have hbr : C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3) ≤ 9 * C * L ^ 2 := by
    calc C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3) ≤ C * (3 * L) * (3 * L) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC) hlog3 hlog0
          positivity
      _ = 9 * C * L ^ 2 := by ring
  have hsq : (C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3)) ^ 2 ≤ 81 * C ^ 2 * L ^ 4 := by
    calc _ ≤ (9 * C * L ^ 2) ^ 2 := pow_le_pow_left₀ hbr0 hbr 2
      _ = 81 * C ^ 2 * L ^ 4 := by ring
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hleft : N + (C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3)) ^ 2 ≤ K * L ^ 4 := by
    have : N ≤ |N| * L ^ 4 := (le_abs_self N).trans (le_mul_of_one_le_right (abs_nonneg N) hL4)
    rw [hK]; nlinarith
  -- the little-o bound
  have h6 : L ^ 6 ≤ c / (2 * (K + 1)) * X ^ 2 := by
    have e1 : ‖Real.log X ^ (6 : ℝ)‖ = L ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have e2 : ‖X ^ (2 : ℝ)‖ = X ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [e1, e2] at hX
    exact hX
  have hmain : K * L ^ 4 * L ^ 2 ≤ c / 2 * X ^ 2 := by
    have : K * L ^ 6 ≤ (K + 1) * L ^ 6 := by nlinarith [pow_pos hL0 6]
    calc K * L ^ 4 * L ^ 2 = K * L ^ 6 := by ring
      _ ≤ (K + 1) * L ^ 6 := this
      _ ≤ (K + 1) * (c / (2 * (K + 1)) * X ^ 2) := mul_le_mul_of_nonneg_left h6 (by linarith)
      _ = c / 2 * X ^ 2 := by field_simp
  calc N + (C * (2 * L + Y + 1) * Real.log (2 * L + Y + 3)) ^ 2 ≤ K * L ^ 4 := hleft
    _ ≤ c / 2 * X ^ 2 / L ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        exact hmain

end GoldbachBoundaries.Paper2.M2
