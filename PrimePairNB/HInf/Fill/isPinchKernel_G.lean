import PrimePairNB.HInf.Defs

/-!
# `isPinchKernel_G`

(K1) is `M4b.kerG_H2a`. (K3) is `M4b.hypR_kerG_WG` on `2 < Re v < 3`. (K2) is direct from (Z6), with `x` running up to
`Re v - ε₀` for each `v`; a bound only for `x ≤ x₂` with a fixed `x₂ < Re v` would not do.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- (K2) for `kerG`, with the range of `x` depending on `v`. -/
lemma decay_kerG (hZ6 : Z6) (C : Set ℂ) (hC : IsCompact C) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ M : ℝ, ∀ v ∈ C, ∀ x y : ℝ, ε₀ ≤ x → x ≤ v.re - ε₀ →
      ‖kerG ((x : ℂ) + (y : ℂ) * I) v‖ ≤ M / (1 + |y|) ^ 2 := by
  obtain ⟨R₀, hR₀⟩ := hC.isBounded.exists_norm_le
  set R : ℝ := max R₀ ε₀ with hRdef
  have hεR : ε₀ ≤ R := le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hnorm : ∀ v ∈ C, ‖v‖ ≤ R := fun v hv => (hR₀ v hv).trans (le_max_left _ _)
  obtain ⟨C₁, hC₁⟩ := hZ6 ε₀ R hε₀ hεR
  have hC₁0 : 0 ≤ C₁ := by
    have h := hC₁ ε₀ ⟨le_rfl, hεR⟩ 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one, mul_zero, zero_div, neg_zero, Real.exp_zero] at h
    exact (norm_nonneg _).trans h
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn
    (f := fun v => (Gamma v)⁻¹) differentiable_one_div_Gamma.continuous.continuousOn
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right _ _
  obtain ⟨K, hK0, hK⟩ := M4a.FillD.exists_rpow_mul_exp_le (R + R)
  set D : ℝ := C₁ * C₁ * (1 + R) ^ R * Real.exp (Real.pi * R / 2) * B' with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * K, fun v hv x y hx1 hx2 => ?_⟩
  set u : ℝ := |y| with hu
  have hu0 : 0 ≤ u := abs_nonneg y
  have hvn := hnorm v hv
  have hvre : v.re ≤ R := (Complex.re_le_norm v).trans hvn
  have hvim : |v.im| ≤ R := (Complex.abs_im_le_norm v).trans hvn
  have hG1 := hC₁ x ⟨hx1, by linarith⟩ y
  have hG2 := hC₁ (v.re - x) ⟨by linarith, by linarith⟩ (v.im - y)
  have hsub : v - ((x : ℂ) + (y : ℂ) * I) = ((v.re - x : ℝ) : ℂ) + ((v.im - y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hty : 1 + |v.im - y| ≤ (1 + R) * (1 + u) := by
    have := abs_sub (v.im) y
    nlinarith
  have hb1 : (1 + |v.im - y|) ^ R ≤ (1 + R) ^ R * (1 + u) ^ R := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hty hRpos.le
  have hb3 : Real.exp (-(Real.pi * |v.im - y| / 2)) ≤
      Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : u - |v.im| ≤ |v.im - y| := by
      have := abs_sub_abs_le_abs_sub y v.im
      rw [abs_sub_comm] at this
      linarith
    have hpi := Real.pi_pos
    nlinarith
  have hinv : ‖(Gamma v)⁻¹‖ ≤ B' := (hB v hv).trans (le_max_left _ _)
  have hexp : Real.exp (-(Real.pi * u / 2)) * Real.exp (-(Real.pi * u / 2)) = Real.exp (-(Real.pi * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow : (1 + u) ^ R * (1 + u) ^ R = (1 + u) ^ (R + R) := by
    rw [Real.rpow_add (by linarith)]
  have hmain : ‖kerG ((x : ℂ) + (y : ℂ) * I) v‖ ≤ D * ((1 + u) ^ (R + R) * Real.exp (-(Real.pi * u))) := by
    have hker : kerG ((x : ℂ) + (y : ℂ) * I) v =
        Gamma ((x : ℂ) + (y : ℂ) * I) * Gamma (v - ((x : ℂ) + (y : ℂ) * I)) * (Gamma v)⁻¹ := by
      simp [kerG, KerS, div_eq_mul_inv]
    rw [hker, norm_mul, norm_mul, hsub]
    calc ‖Gamma ((x : ℂ) + (y : ℂ) * I)‖ * ‖Gamma (((v.re - x : ℝ) : ℂ) + ((v.im - y : ℝ) : ℂ) * I)‖ * ‖(Gamma v)⁻¹‖
        ≤ (C₁ * (1 + u) ^ R * Real.exp (-(Real.pi * u / 2))) *
            (C₁ * ((1 + R) ^ R * (1 + u) ^ R) *
              (Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2)))) * B' := by
          gcongr
          · exact hG2.trans (by gcongr)
      _ = D * (((1 + u) ^ R * (1 + u) ^ R) *
            (Real.exp (-(Real.pi * u / 2)) * Real.exp (-(Real.pi * u / 2)))) := by
          rw [hD]
          ring
      _ = _ := by rw [hrpow, hexp]
  calc _ ≤ D * ((1 + u) ^ (R + R) * Real.exp (-(Real.pi * u))) := hmain
    _ ≤ D * (K / (1 + u) ^ 2) := by gcongr; exact hK u hu0
    _ = D * K / (1 + u) ^ 2 := by ring

/-- (K1) to (K3) for `G`: `𝒱 = {Re v > 1}`. -/
theorem isPinchKernel_G (hZ6 : Z6) : IsPinchKernel kerG ⊤ G := by
  refine ⟨le_top, ?_, ?_, ?_⟩
  · refine M4b.kerG_H2a.mono ?_
    rintro ⟨z, v⟩ ⟨hv, hz0, hz1⟩
    have happ : Aff.idL.app v = v := by simp [Aff.app, Aff.idL]
    refine ⟨?_, hz0, ?_⟩
    · show 1 < (Aff.idL.app v).re
      rw [happ]
      exact hv.1
    · show z.re < (Aff.idL.app v).re
      rw [happ]
      exact hz1
  · intro C hC _ ε₀ hε₀
    exact decay_kerG hZ6 C hC ε₀ hε₀
  · intro v h2 h3 c hc1 hc2
    have happ : Aff.idL.app v = v := by simp [Aff.app, Aff.idL]
    have h := M4b.hypR_kerG_WG.2.2.2 v
      ⟨by show 2 < (Aff.idL.app v).re; rw [happ]; exact h2,
        by show 1 < (Aff.idL.app v).re ∧ (Aff.idL.app v).re < 3; rw [happ]; exact ⟨by linarith, h3⟩⟩
      c hc1 (by rw [happ]; exact hc2)
    rw [happ] at h
    exact h

end GoldbachBoundaries.HInf.Fill

