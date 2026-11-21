import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.sum_zetaMult_window_le

/-! `norm_negLogDerivZeta_le_strip`. (Z3) with every zero of its window at
distance `≥ δ` from `w` (good height), and the window count of `sum_zetaMult_window_le`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `log(y + 3) ≤ 3 log y` for `y ≥ 2`. -/
lemma log_add_three_le_three_mul_log {y : ℝ} (hy : 2 ≤ y) : Real.log (y + 3) ≤ 3 * Real.log y := by
  rw [show (3 : ℝ) * Real.log y = ((3 : ℕ) : ℝ) * Real.log y by norm_num, ← Real.log_pow]
  have h4 : 4 ≤ y ^ 2 := by nlinarith
  exact Real.log_le_log (by linarith) (by nlinarith)

/-- **The `k = 1` term in the strip** (Z1, Z2, Z3): for `δ > 0` there is `C` (before `H`) such that for every good
height `H` and `B_∞ + 2δ ≤ Re w ≤ 2`, `|Im w| ≥ H`: `ζ(w) ≠ 0` and `|A(w)| ≤ C log |Im w|`. In (Z3) every zero of the
sum has `|γ| ≥ |Im w| - 1 ≥ H - 1`, so `β ≤ B_∞ + δ` and `|w - ρ| ≥ δ`; the sum is at most
`δ⁻¹ ∑ m(ρ) ≪ log |Im w|` (`sum_zetaMult_window_le`). Uses: `sum_zetaMult_window_le`, `half_le_Binf` (so that
`Re w ≥ -1`). -/
theorem norm_negLogDerivZeta_le_strip (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ H : ℝ, GoodHeight δ H → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → w.re ≤ 2 → H ≤ |w.im| →
      riemannZeta w ≠ 0 ∧ ‖negLogDerivZeta w‖ ≤ C * Real.log |w.im| := by
  obtain ⟨C₃, hC₃⟩ := hZ3
  obtain ⟨C₂, hC₂⟩ := sum_zetaMult_window_le hZ1 hZ2
  set C₂' := max C₂ 0 with hC₂'def
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  refine ⟨C₃ + 3 * C₂' / δ, fun H hH w hw1 hw2 hwH => ?_⟩
  have hB0 := Binf_nonneg
  have hy2 : 2 ≤ |w.im| := hH.1.trans hwH
  -- zeros in the window of `w` are at distance `≥ δ`
  have hfar : ∀ ρ ∈ NontrivialZeros, |ρ.im - w.im| ≤ 1 → δ ≤ ‖w - ρ‖ := by
    intro ρ hρ h1
    have hρH : H - 1 ≤ |ρ.im| := by
      have := abs_sub_abs_le_abs_sub w.im ρ.im
      rw [abs_sub_comm] at h1
      linarith
    have hre := hH.2 ρ hρ hρH
    calc δ ≤ (w - ρ).re := by simp only [sub_re]; linarith
      _ ≤ |(w - ρ).re| := le_abs_self _
      _ ≤ ‖w - ρ‖ := Complex.abs_re_le_norm _
  have hζ : riemannZeta w ≠ 0 := by
    intro h0
    have hw1' : w.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h h0
    have hwZ : w ∈ NontrivialZeros := ⟨h0, by linarith, hw1'⟩
    have := hfar w hwZ (by simp)
    simp only [sub_self, norm_zero] at this
    linarith
  refine ⟨hζ, ?_⟩
  obtain ⟨hWfin, hWsum⟩ := hC₂ w.im
  set W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - w.im| ≤ 1} with hWdef
  have hz3 := hC₃ w (by linarith) hw2 hy2 hζ
  have hsum : ‖∑ᶠ ρ ∈ W, (zetaMult ρ : ℂ) / (w - ρ)‖ ≤ (1 / δ) * ∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [Set.Finite.mem_toFinset] at hρ
    have hd := hfar ρ hρ.1 hρ.2
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hd).trans_eq (by ring)
  have hlog := log_add_three_le_three_mul_log hy2
  have hlog0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
  have hS : (1 / δ) * ∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ) ≤ 3 * C₂' / δ * Real.log |w.im| := by
    have h1 : ∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ) ≤ C₂' * Real.log (|w.im| + 3) :=
      hWsum.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.log_nonneg (by linarith [abs_nonneg w.im])))
    have h2 : C₂' * Real.log (|w.im| + 3) ≤ C₂' * (3 * Real.log |w.im|) :=
      mul_le_mul_of_nonneg_left hlog hC₂'0
    have h3 : (1 / δ) * (C₂' * (3 * Real.log |w.im|)) = 3 * C₂' / δ * Real.log |w.im| := by
      field_simp
    rw [← h3]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  set S := ∑ᶠ ρ ∈ W, (zetaMult ρ : ℂ) / (w - ρ)
  calc ‖negLogDerivZeta w‖ = ‖deriv riemannZeta w / riemannZeta w - S + S‖ := by
        rw [negLogDerivZeta, norm_neg, sub_add_cancel]
    _ ≤ ‖deriv riemannZeta w / riemannZeta w - S‖ + ‖S‖ := norm_add_le _ _
    _ ≤ C₃ * Real.log |w.im| + 3 * C₂' / δ * Real.log |w.im| := add_le_add hz3 (hsum.trans hS)
    _ = (C₃ + 3 * C₂' / δ) * Real.log |w.im| := by ring

end GoldbachBoundaries.Paper2.M1
