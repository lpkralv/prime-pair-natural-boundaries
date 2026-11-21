import PrimePairNB.ThmA.G20_Branches

/-!
# Shared helpers (access discs, jump, branches)

Elementary geometry of discs centred on the line `α + ℝ v` and the identity theorem from an open
subset. Used by `jump_of_access` and `isBranch_uniform_cut`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- Identity theorem from a nonempty open subset of a preconnected set. -/
theorem G_eqOn_of_subset {f g : ℂ → ℂ} {U W : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) (hW : IsOpen W) (hWU : W ⊆ U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ W) (hfg : EqOn f g W) : EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hWU hz₀)
    (Filter.eventuallyEq_of_mem (hW.mem_nhds hz₀) hfg)

theorem G_one_le_norm_slantDir (κ : ℝ) : 1 ≤ ‖slantDir κ‖ := by
  have h := Complex.abs_re_le_norm (slantDir κ)
  have : (slantDir κ).re = 1 := by simp [slantDir]
  rw [this, abs_one] at h
  exact h

/-- Points of a cut lie on the line `Im((s-α)/v) = 0`. -/
theorem G_im_cut {κ : ℝ} {α s : ℂ} (hs : s ∈ cut (slantDir κ) α) :
    ((s - α) / slantDir κ).im = 0 := by
  obtain ⟨t, -, -, rfl⟩ := hs
  have hv := slantDir_ne_zero κ
  have : (α - (t : ℂ) * slantDir κ - α) / slantDir κ = -(t : ℂ) := by field_simp; ring
  rw [this]; simp

/-- Near a point of the line there are points on both sides. -/
theorem G_exists_upper_lower {κ : ℝ} {α p : ℂ} {U : Set ℂ} (hU : IsOpen U) (hp : p ∈ U)
    (hpl : ((p - α) / slantDir κ).im = 0) :
    (∃ z ∈ U, 0 < ((z - α) / slantDir κ).im) ∧ (∃ z ∈ U, ((z - α) / slantDir κ).im < 0) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hv := slantDir_ne_zero κ
  have hnv : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hv
  set c : ℝ := ε / (2 * ‖slantDir κ‖) with hcdef
  have hc : 0 < c := by positivity
  have key : ∀ d : ℝ, |d| = c → p + (d : ℂ) * I * slantDir κ ∈ U ∧
      ((p + (d : ℂ) * I * slantDir κ - α) / slantDir κ).im = d := by
    intro d hd
    constructor
    · apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, hd, hcdef]
      field_simp
      linarith
    · have : (p + (d : ℂ) * I * slantDir κ - α) / slantDir κ = (p - α) / slantDir κ + d * I := by
        field_simp; ring
      rw [this]; simp [hpl]
  refine ⟨⟨_, (key c (abs_of_pos hc)).1, ?_⟩, ⟨_, (key (-c) (by rw [abs_neg, abs_of_pos hc])).1, ?_⟩⟩
  · rw [(key c (abs_of_pos hc)).2]; exact hc
  · rw [(key (-c) (by rw [abs_neg, abs_of_pos hc])).2]; linarith

/-- Projection onto the line `α + ℝ v` does not increase the distance to a point of the line. -/
theorem G_proj {κ : ℝ} {α s₁ : ℂ} (h₁ : ((s₁ - α) / slantDir κ).im = 0) (z : ℂ) :
    dist (α + (((z - α) / slantDir κ).re : ℂ) * slantDir κ) s₁ ≤ dist z s₁ ∧
    ((α + (((z - α) / slantDir κ).re : ℂ) * slantDir κ - α) / slantDir κ).im = 0 := by
  have hv := slantDir_ne_zero κ
  set w := (z - α) / slantDir κ with hw
  set w₁ := (s₁ - α) / slantDir κ with hw₁
  have hz : z - s₁ = slantDir κ * (w - w₁) := by rw [hw, hw₁]; field_simp; ring
  have hs₁ : s₁ = α + w₁ * slantDir κ := by rw [hw₁]; field_simp; ring
  have hw₁r : w₁ = (w₁.re : ℂ) := Complex.ext (by simp) (by simp [h₁])
  have hp : α + (w.re : ℂ) * slantDir κ - s₁ = slantDir κ * (((w - w₁).re : ℝ) : ℂ) := by
    rw [hs₁, sub_re]
    push_cast
    rw [← hw₁r]; ring
  constructor
  · rw [dist_eq_norm, dist_eq_norm, hp, hz, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)
  · have : (α + (w.re : ℂ) * slantDir κ - α) / slantDir κ = (w.re : ℂ) := by field_simp; ring
    rw [this]; simp

/-- Two discs centred on the line `α + ℝ v` that meet: their intersection has points on both
sides of the line. -/
theorem G_inter_upper_lower {κ : ℝ} {α s₁ s₂ : ℂ} (h₁ : ((s₁ - α) / slantDir κ).im = 0)
    (h₂ : ((s₂ - α) / slantDir κ).im = 0) {ρ₁ ρ₂ : ℝ} (hne : (ball s₁ ρ₁ ∩ ball s₂ ρ₂).Nonempty) :
    (∃ z ∈ ball s₁ ρ₁ ∩ ball s₂ ρ₂, 0 < ((z - α) / slantDir κ).im) ∧
    (∃ z ∈ ball s₁ ρ₁ ∩ ball s₂ ρ₂, ((z - α) / slantDir κ).im < 0) := by
  obtain ⟨z, hz1, hz2⟩ := hne
  obtain ⟨hd1, hl⟩ := G_proj h₁ z
  obtain ⟨hd2, -⟩ := G_proj h₂ z
  refine G_exists_upper_lower (isOpen_ball.inter isOpen_ball) ⟨?_, ?_⟩ hl
  · exact mem_ball.mpr (lt_of_le_of_lt hd1 (mem_ball.mp hz1))
  · exact mem_ball.mpr (lt_of_le_of_lt hd2 (mem_ball.mp hz2))

theorem G_log_upper {w : ℂ} (hw : 0 < w.im) : Complex.log w = Complex.log (-w) + Real.pi * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast; ring

theorem G_log_lower {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) + Real.pi * I = Complex.log w + 2 * Real.pi * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  push_cast; ring

end GoldbachBoundaries.ThmA
