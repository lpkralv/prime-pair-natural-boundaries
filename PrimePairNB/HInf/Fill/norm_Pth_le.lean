import PrimePairNB.HInf.Fill.hasDerivAt_Pth

/-! Proof of `norm_Pth_le`, with (Z1), (Z2), (Z3) through
`M1.norm_Qcont_le_growth`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
open scoped Interval

namespace GoldbachBoundaries.HInf.Fill

/-- `|P(s)| ≤ ∑_p p^{-2}` on `Re s ≥ 2`. -/
lemma norm_P_le_two {s : ℂ} (hs : 2 ≤ s.re) :
    ‖P s‖ ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(2 : ℂ))‖ := by
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hs1 : 1 < s.re := by linarith
  unfold P
  refine (norm_tsum_le_tsum_norm (summable_norm_P_terms hs1)).trans ?_
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_norm_P_terms hs1) (summable_norm_P_terms h2)
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  apply Real.rpow_le_rpow_of_exponent_le hp
  simp only [neg_re, re_ofNat]
  linarith

/-- For `η > 0` there are `T`, `C` with `z ∈ U_θ` and `|P^θ(z)| ≤ C log(|Im z| + 2)` on
`Re z ≥ B_∞ + 2η`, `|Im z| ≥ T`. Premises (Z1), (Z2), (Z3): (Z3) stands in place of the Borel–Carathéodory argument. -/
theorem norm_Pth_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (κ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T C : ℝ, ∀ z : ℂ, Binf + 2 * η ≤ z.re → T ≤ |z.im| →
      z ∈ Uth κ ∧ ‖Pth κ z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨C₀, hC₀⟩ := M1.norm_Qcont_le_growth hZ1 hZ2 hZ3 η hη
  obtain ⟨H, hH⟩ := M1.exists_goodHeight η hη
  have hB : (1 : ℝ) / 2 ≤ Binf := M1.half_le_Binf hZ1
  have hH2 : 2 ≤ H := hH.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(2 : ℂ))‖ with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  set w : ℂ := slantDir κ with hw
  set M₀ : ℝ := max C₀ 0 with hM₀
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  set A : ℝ := Real.log (1 + |κ|) with hA
  have hA0 : 0 ≤ A := Real.log_nonneg (by linarith [abs_nonneg κ])
  refine ⟨H + 2 * |κ|, B / Real.log 2 + ‖w‖ * (M₀ * (1 + A / Real.log 2) * 2), fun z hre hT => ?_⟩
  have hk0 := abs_nonneg κ
  have hy2 : 2 ≤ |z.im| := by linarith
  -- points of the segment stay in the region of `norm_Qcont_le_growth`
  have him_lower : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 2 → H ≤ |(z + (τ : ℂ) * w).im| := by
    intro τ h0 h2
    rw [hw, im_add_mul_slantDir]
    have h3 : |τ * κ| ≤ 2 * |κ| := by
      rw [abs_mul, abs_of_nonneg h0]
      nlinarith
    have h4 : |z.im| ≤ |z.im + τ * κ| + |τ * κ| := by
      have := abs_add_le (z.im + τ * κ) (-(τ * κ))
      simpa using this
    linarith
  have him_upper : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 2 → |(z + (τ : ℂ) * w).im| ≤ |z.im| + 2 * |κ| := by
    intro τ h0 h2
    rw [hw, im_add_mul_slantDir]
    have h3 : |τ * κ| ≤ 2 * |κ| := by
      rw [abs_mul, abs_of_nonneg h0]
      nlinarith
    have := abs_add_le z.im (τ * κ)
    linarith
  constructor
  · -- `z ∈ U_θ`
    refine ⟨(show 0 < z.re by linarith), fun h => ?_⟩
    obtain ⟨a, ha, t, ht, he⟩ := mem_iUnion₂.mp h
    have hae : a = z + (t : ℂ) * w := by
      rw [he]
      ring
    have hb := M1.poleSetQ_re_bounds ha
    have hare : a.re = z.re + t := by
      rw [hae, hw, re_add_mul_slantDir]
    have ht2 : t ≤ 2 := by linarith [hb.2.1]
    have hH' : H ≤ |a.im| := by
      rw [hae]
      exact him_lower t ht ht2
    exact (hC₀ H hH a (by linarith) hH').1 ha
  · -- the bound
    set L : ℝ := Real.log (|z.im| + 2) with hL
    have hL0 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have hLpos : 0 < L := by linarith
    have hAL : A ≤ A / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hL0 hA0
    have hBL : B ≤ B / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hL0 hB0
    have hint : ∀ τ ∈ Ι (0 : ℝ) 2, ‖Qcont (z + (τ : ℂ) * w)‖ ≤ M₀ * (1 + A / Real.log 2) * L := by
      intro τ hτ
      rw [uIoc_of_le (by norm_num)] at hτ
      have h0 : 0 ≤ τ := hτ.1.le
      have h2 := hτ.2
      have hlow := him_lower τ h0 h2
      have hup := him_upper τ h0 h2
      have hreu : Binf + 2 * η ≤ (z + (τ : ℂ) * w).re := by
        rw [hw, re_add_mul_slantDir]
        linarith
      have h5 := (hC₀ H hH _ hreu hlow).2
      have hupos : 0 < |(z + (τ : ℂ) * w).im| := by linarith
      have hlogu0 : 0 ≤ Real.log |(z + (τ : ℂ) * w).im| := Real.log_nonneg (by linarith)
      have hlogu : Real.log |(z + (τ : ℂ) * w).im| ≤ L + A := by
        rw [hL, hA, ← Real.log_mul (by linarith) (by linarith)]
        apply Real.log_le_log hupos
        nlinarith
      calc ‖Qcont (z + (τ : ℂ) * w)‖
          ≤ C₀ * Real.log |(z + (τ : ℂ) * w).im| := h5
        _ ≤ M₀ * Real.log |(z + (τ : ℂ) * w).im| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hlogu0
        _ ≤ M₀ * (L + A) := mul_le_mul_of_nonneg_left hlogu hM₀0
        _ ≤ M₀ * (1 + A / Real.log 2) * L := by
            have : L + A ≤ (1 + A / Real.log 2) * L := by linarith
            calc M₀ * (L + A) ≤ M₀ * ((1 + A / Real.log 2) * L) :=
                  mul_le_mul_of_nonneg_left this hM₀0
              _ = _ := by ring
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hint
    have hIe : |(2 : ℝ) - 0| = 2 := by norm_num
    rw [hIe] at hI
    have hPb : ‖P (z + 2 * w)‖ ≤ B := by
      apply norm_P_le_two
      have := re_add_mul_slantDir κ z 2
      simp only [ofReal_ofNat] at this
      rw [hw, this]
      linarith
    have hval : Pth κ z = P (z + 2 * w) + w * ∫ τ in (0 : ℝ)..2, Qcont (z + (τ : ℂ) * w) := rfl
    rw [hval]
    calc ‖P (z + 2 * w) + w * ∫ τ in (0 : ℝ)..2, Qcont (z + (τ : ℂ) * w)‖
        ≤ ‖P (z + 2 * w)‖ + ‖w‖ * ‖∫ τ in (0 : ℝ)..2, Qcont (z + (τ : ℂ) * w)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ B / Real.log 2 * L + ‖w‖ * (M₀ * (1 + A / Real.log 2) * L * 2) := by
          have := mul_le_mul_of_nonneg_left hI (norm_nonneg w)
          linarith
      _ = (B / Real.log 2 + ‖w‖ * (M₀ * (1 + A / Real.log 2) * 2)) * L := by ring

end GoldbachBoundaries.HInf.Fill
