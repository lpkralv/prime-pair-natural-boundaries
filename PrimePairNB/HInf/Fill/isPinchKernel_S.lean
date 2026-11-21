import PrimePairNB.HInf.Defs

/-!
# `isPinchKernel_S`

(K1) is `M4b.kerS_basic`, in the variable `s = (v - 1)/2`. (K3) is `M4b.hypR_kerS` in the same variable. (K2) is elementary
from `K(w) = (1 - w)π / sin πw`, with no (Z6): for `|Im w| ≥ 1` this and `|sin πw| ≥ sinh π|Im w|` give the decay, and on
`|Im w| ≤ 1` the kernel is continuous on a compact rectangle.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `|sin z| ≥ |sinh (Im z)|`. -/
lemma abs_sinh_im_le_norm_sin (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
  have e : Complex.sin z = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ) +
      ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
    rw [Complex.sin_eq]
    push_cast
    ring
  have hre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [e]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    rw [e]
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  have hsq : Real.sinh z.im ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have : (Real.sin z.re * Real.cosh z.im) * (Real.sin z.re * Real.cosh z.im) +
        (Real.cos z.re * Real.sinh z.im) * (Real.cos z.re * Real.sinh z.im) =
        Real.sinh z.im ^ 2 + Real.sin z.re ^ 2 := by
      have hc : Real.cos z.re ^ 2 = 1 - Real.sin z.re ^ 2 := by linarith
      calc _ = Real.sin z.re ^ 2 * Real.cosh z.im ^ 2 + Real.cos z.re ^ 2 * Real.sinh z.im ^ 2 := by ring
        _ = _ := by rw [h2, hc]; ring
    rw [this]
    nlinarith [sq_nonneg (Real.sin z.re)]
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |> fun h => abs_le.mpr ⟨h.1, h.2⟩

/-- For `τ ≥ 1`, `τ³ ≤ sinh (π τ)`. -/
lemma cube_le_sinh_pi {τ : ℝ} (hτ : 1 ≤ τ) : τ ^ 3 ≤ Real.sinh (Real.pi * τ) := by
  have hpi := Real.pi_gt_three
  set x : ℝ := Real.pi * τ with hx
  have hx3 : 3 * τ ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 ≤ x := by linarith
  have h1 : x ^ 3 / 6 ≤ Real.exp x := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp x hx0 3
  have hexpinv : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp1 : 3 ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have hsinh : Real.exp x / 3 ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  have hpow : (3 * τ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by linarith) hx3 3
  have hτ3 : 0 ≤ τ ^ 3 := by positivity
  have : (3 * τ) ^ 3 = 27 * τ ^ 3 := by ring
  linarith

/-- `K(w) = (1 - w) π / sin πw`, off the real axis. -/
lemma KS_eq_of_im_ne {w : ℂ} (h : w.im ≠ 0) :
    KS w = (1 - w) * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
  have h1 : (1 - w) ≠ 0 := by
    intro h0
    apply h
    have : w = 1 := by linear_combination -h0
    simp [this]
  have hG : Gamma (2 - w) = (1 - w) * Gamma (1 - w) := by
    rw [show (2 : ℂ) - w = (1 - w) + 1 by ring, Complex.Gamma_add_one _ h1]
  rw [KS, hG, ← Complex.Gamma_mul_Gamma_one_sub]
  ring

/-- The decay of `K` for `|Im w| ≥ 1`, for `0 ≤ Re w ≤ 2`. -/
lemma norm_KS_mul_sq_le_of_one_le {w : ℂ} (h0 : 0 ≤ w.re) (h2 : w.re ≤ 2) (him : 1 ≤ |w.im|) :
    ‖KS w‖ * (1 + |w.im|) ^ 2 ≤ 8 * Real.pi := by
  set τ : ℝ := |w.im| with hτ
  have hne : w.im ≠ 0 := by
    intro h
    rw [hτ, h, abs_zero] at him
    linarith
  have hpi := Real.pi_pos
  have hsinh : τ ^ 3 ≤ ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by
    have h := abs_sinh_im_le_norm_sin ((Real.pi : ℂ) * w)
    have him' : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
    rw [him'] at h
    have h3 : Real.sinh (Real.pi * τ) ≤ |Real.sinh (Real.pi * w.im)| := by
      rcases abs_cases w.im with ⟨h4, _⟩ | ⟨h4, _⟩
      · rw [hτ, h4]
        exact le_abs_self _
      · rw [hτ, h4, mul_neg, Real.sinh_neg]
        exact neg_le_abs _
    exact (cube_le_sinh_pi him).trans (h3.trans h)
  have hτ0 : 0 < τ := by linarith
  have hτ3 : 0 < τ ^ 3 := by positivity
  have h1w : ‖1 - w‖ ≤ 1 + τ := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - w)
    have hre : |(1 - w).re| ≤ 1 := by
      rw [abs_le]
      simp only [sub_re, one_re]
      constructor <;> linarith
    have hIm : |(1 - w).im| = τ := by simp [hτ]
    linarith
  rw [KS_eq_of_im_ne hne, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hdiv : Real.pi / ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤ Real.pi / τ ^ 3 :=
    div_le_div_of_nonneg_left hpi.le hτ3 hsinh
  have hτ1 : 1 + τ ≤ 2 * τ := by linarith
  calc ‖1 - w‖ * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * w)‖) * (1 + τ) ^ 2
      ≤ (1 + τ) * (Real.pi / τ ^ 3) * (1 + τ) ^ 2 := by gcongr
    _ = (1 + τ) ^ 3 * (Real.pi / τ ^ 3) := by ring
    _ ≤ (2 * τ) ^ 3 * (Real.pi / τ ^ 3) := by gcongr
    _ = 8 * Real.pi := by field_simp; ring

/-- `K` is continuous on `Re w > 0, Re w < 2`. -/
lemma continuousOn_KS : ContinuousOn KS {w : ℂ | 0 < w.re ∧ w.re < 2} := by
  intro w hw
  have h1 : DifferentiableAt ℂ Gamma w := M4b.FillD.differentiableAt_Gamma_of_re_pos hw.1
  have h2 : DifferentiableAt ℂ Gamma (2 - w) :=
    M4b.FillD.differentiableAt_Gamma_of_re_pos (by simp; linarith [hw.2])
  have h3 : ContinuousAt (fun w : ℂ => Gamma (2 - w)) w :=
    ContinuousAt.comp (f := fun w : ℂ => 2 - w) (g := Gamma) h2.continuousAt (by fun_prop)
  exact (h1.continuousAt.mul h3).continuousWithinAt

/-- Uniform decay of `K` on a closed strip inside `0 < Re w < 2`. -/
lemma exists_KS_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ε ≤ w.re → w.re ≤ 2 - ε → ‖KS w‖ * (1 + |w.im|) ^ 2 ≤ M := by
  set R : Set ℂ := Icc ε (2 - ε) ×ℂ Icc (-1) 1 with hR
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn KS R := continuousOn_KS.mono (by
    intro w hw
    have h1 := hw.1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩)
  obtain ⟨B, hB⟩ := hRc.exists_bound_of_continuousOn hcont
  refine ⟨max (B * 4) (8 * Real.pi), le_max_of_le_right (by positivity), fun w h1 h2 => ?_⟩
  by_cases him : 1 ≤ |w.im|
  · exact le_max_of_le_right (norm_KS_mul_sq_le_of_one_le (by linarith) (by linarith) him)
  · refine le_max_of_le_left ?_
    rw [not_le] at him
    have hmem : w ∈ R := ⟨⟨h1, h2⟩, ⟨by linarith [(abs_lt.mp him).1], by linarith [(abs_lt.mp him).2]⟩⟩
    have hb := hB w hmem
    have h4 : (1 + |w.im|) ^ 2 ≤ 4 := by
      have := abs_nonneg w.im
      nlinarith
    calc ‖KS w‖ * (1 + |w.im|) ^ 2 ≤ B * 4 := by
          exact mul_le_mul hb h4 (by positivity) ((norm_nonneg _).trans hb)

/-- `Re v < 3` on `Vt 3`. -/
lemma re_lt_three_of_mem {v : ℂ} (h : v ∈ Vt 3) : v.re < 3 :=
  EReal.coe_lt_coe_iff.mp (h.2.trans_eq (by norm_cast))

/-- (K2) for `kS`. -/
lemma decay_kS (C : Set ℂ) (hC : IsCompact C) (hCV : C ⊆ Vt 3) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ M : ℝ, ∀ v ∈ C, ∀ x y : ℝ, ε₀ ≤ x → x ≤ v.re - ε₀ →
      ‖kS ((x : ℂ) + (y : ℂ) * I) v‖ ≤ M / (1 + |y|) ^ 2 := by
  obtain ⟨R₀, hR₀⟩ := hC.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  obtain ⟨M, hM0, hM⟩ := exists_KS_bound (ε := ε₀ / 2) (by positivity)
  refine ⟨(1 / 2) * (M * (2 + R) ^ 2), fun v hv x y hx1 hx2 => ?_⟩
  have hvV := hCV hv
  have hv3 : v.re < 3 := re_lt_three_of_mem hvV
  have hvim : |v.im| ≤ R := (Complex.abs_im_le_norm v).trans ((hR₀ v hv).trans (le_max_left _ _))
  set w : ℂ := ((x : ℂ) + (y : ℂ) * I - (v - 1) / 2 + 1) / 2 with hw
  have hwre : w.re = (x - (v.re - 1) / 2 + 1) / 2 := by
    simp [hw]
  have hwim : w.im = (y - v.im / 2) / 2 := by
    simp [hw]
  have hb := hM w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
  have hk : kS ((x : ℂ) + (y : ℂ) * I) v = (1 / 2) * KS w := rfl
  have hy : 1 + |y| ≤ (2 + R) * (1 + |w.im|) := by
    have h1 : y = 2 * w.im + v.im / 2 := by rw [hwim]; ring
    have h2 : |y| ≤ 2 * |w.im| + |v.im| / 2 := by
      rw [h1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_div, abs_two]
    have h3 := abs_nonneg w.im
    nlinarith
  have hypos : 0 < (1 + |y|) ^ 2 := by positivity
  rw [hk, norm_mul, le_div_iff₀ hypos]
  have hsq : (1 + |y|) ^ 2 ≤ (2 + R) ^ 2 * (1 + |w.im|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hy 2
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hnorm]
  calc (1 / 2) * ‖KS w‖ * (1 + |y|) ^ 2
      ≤ (1 / 2) * ‖KS w‖ * ((2 + R) ^ 2 * (1 + |w.im|) ^ 2) := by gcongr
    _ = (1 / 2) * ((‖KS w‖ * (1 + |w.im|) ^ 2) * (2 + R) ^ 2) := by ring
    _ ≤ (1 / 2) * (M * (2 + R) ^ 2) := by gcongr

/-- `L((v - 1)/2) = v`. -/
lemma app_twoOneL_half (v : ℂ) : Aff.twoOneL.app ((v - 1) / 2) = v := by
  simp only [Aff.app, Aff.twoOneL]
  push_cast
  ring

/-- (K1) for `kS`. -/
lemma holo_kS : DifferentiableOn ℂ (fun p : ℂ × ℂ => kS p.1 p.2) (domK 3) := by
  have hmap : DifferentiableOn ℂ (fun p : ℂ × ℂ => (p.1, (p.2 - 1) / 2)) (domK 3) :=
    (by fun_prop : Differentiable ℂ (fun p : ℂ × ℂ => (p.1, (p.2 - 1) / 2))).differentiableOn
  have hK1 : DifferentiableOn ℂ (fun p : ℂ × ℂ => kerS p.1 p.2) Aff.twoOneL.domK1 := M4b.kerS_basic.1
  have hsub : MapsTo (fun p : ℂ × ℂ => (p.1, (p.2 - 1) / 2)) (domK 3) Aff.twoOneL.domK1 := by
    rintro ⟨z, v⟩ ⟨hv, hz0, hz1⟩
    have hv3 : v.re < 3 := re_lt_three_of_mem hv
    refine ⟨?_, hz0, ?_⟩
    · show 1 < (Aff.twoOneL.app ((v - 1) / 2)).re ∧ (Aff.twoOneL.app ((v - 1) / 2)).re < 3
      rw [app_twoOneL_half]
      exact ⟨hv.1, hv3⟩
    · show z.re < (Aff.twoOneL.app ((v - 1) / 2)).re
      rw [app_twoOneL_half]
      exact hz1
  have h := DifferentiableOn.comp (g := fun p : ℂ × ℂ => kerS p.1 p.2)
    (f := fun p : ℂ × ℂ => (p.1, (p.2 - 1) / 2)) hK1 hmap hsub
  exact h

/-- (K3) for `kS`. -/
lemma mb_kS (v : ℂ) (h2 : 2 < v.re) (h3 : v.re < 3) (c : ℝ) (hc1 : 1 < c) (hc2 : c < v.re - 1) :
    DS v = VerticalIntegral' (fun z => kS z v * P z * P (v - z)) c := by
  have h := M4b.hypR_kerS.2.2.2 ((v - 1) / 2)
    ⟨by show 2 < (Aff.twoOneL.app ((v - 1) / 2)).re; rw [app_twoOneL_half]; exact h2,
      by
        show 1 < (Aff.twoOneL.app ((v - 1) / 2)).re ∧ (Aff.twoOneL.app ((v - 1) / 2)).re < 3
        rw [app_twoOneL_half]
        exact ⟨by linarith, h3⟩⟩
    c hc1 (by rw [app_twoOneL_half]; exact hc2)
  rw [app_twoOneL_half] at h
  exact h

/-- (K1) to (K3) for `S`: `𝒱 = {1 < Re v < 3}`. The one place `Re v < 3` is used is (K1). -/
theorem isPinchKernel_S : IsPinchKernel kS 3 DS where
  three_le := le_refl _
  holo := holo_kS
  decay := decay_kS
  mb := mb_kS

end GoldbachBoundaries.HInf.Fill

