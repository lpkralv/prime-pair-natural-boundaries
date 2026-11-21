import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.Dc_eq_diag
import PrimePairNB.ThmA.Fill.cauchyInt
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

/-!
# `Dc_access_two` (the access lemma (ii),(iii) for `𝒟`)

Proof. `Dc_eq_diag` (upper-side points are off `𝒮 + 𝒮`, since a point of `𝒮 + 𝒮` has
`(s - s₀)/v` real). With `δ = (s - s₀)/v`, `(s - 2)/v = δ - t₀`. `phiD` agrees on `[0, 1-b]` with
`f₁(z) = segInt (u ↦ Γ(1-uv)Γ(1-(z-u)v)) 0 z` and on `[1-b, 2(1-b)]` with
`f₂(z) = segInt (…) (z - (1-b)) (1-b)`, both holomorphic near those real intervals. Choose `η` so
that `[t₀ - η, t₀ + η]` lies inside the open interval on the side of `1-b` where `t₀` is, and split
`∫_0^{2(1-b)}` at `t₀ ± η`: the two outer pieces are holomorphic in `δ` for `|δ| < η/2`
(`differentiableOn_intervalIntegral_of_continuousOn`), and the middle piece continues across by
`cauchyInt`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace DcAccessTwo

theorem gamma_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma s fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

theorem conv_lt_one {X Y τ : ℝ} (hX : X < 1) (hY : Y < 1) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (1 - τ) * X + τ * Y < 1 := by
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left X Y) (sub_nonneg.mpr h1),
    mul_le_mul_of_nonneg_left (le_max_right X Y) h0, max_lt hX hY]

theorem re_conv (A B : ℂ) (τ : ℝ) :
    ((1 - (τ : ℂ)) * A + (τ : ℂ) * B).re = (1 - τ) * A.re + τ * B.re := by
  simp [Complex.add_re, Complex.mul_re]

/-- The integrand of `phiD` with a complex parameter. -/
def kG (v z u : ℂ) : ℂ := Gamma (1 - u * v) * Gamma (1 - (z - u) * v)

/-- Holomorphy of `z ↦ segInt (kG v z) (p z) (q z)` where all Gamma arguments have positive real
part. -/
theorem segGamma_differentiableOn {v : ℂ} {p q : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) {W : Set ℂ} (hW : IsOpen W)
    (h1 : ∀ z ∈ W, (p z * v).re < 1) (h2 : ∀ z ∈ W, (q z * v).re < 1)
    (h3 : ∀ z ∈ W, ((z - p z) * v).re < 1) (h4 : ∀ z ∈ W, ((z - q z) * v).re < 1) :
    DifferentiableOn ℂ (fun z => segInt (kG v z) (p z) (q z)) W := by
  have hpos : ∀ z ∈ W, ∀ τ ∈ [[(0 : ℝ), 1]],
      0 < (1 - (p z + (τ : ℂ) * (q z - p z)) * v).re ∧
      0 < (1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v).re := by
    intro z hz τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have e1 : (1 - (p z + (τ : ℂ) * (q z - p z)) * v) =
        1 - ((1 - (τ : ℂ)) * (p z * v) + (τ : ℂ) * (q z * v)) := by ring
    have e2 : (1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v) =
        1 - ((1 - (τ : ℂ)) * ((z - p z) * v) + (τ : ℂ) * ((z - q z) * v)) := by ring
    rw [e1, e2, sub_re, sub_re, one_re, re_conv, re_conv]
    exact ⟨by linarith [conv_lt_one (h1 z hz) (h2 z hz) hτ.1 hτ.2],
      by linarith [conv_lt_one (h3 z hz) (h4 z hz) hτ.1 hτ.2]⟩
  have hpc := hp.continuous
  have hqc := hq.continuous
  simp only [segInt, kG]
  refine (hq.sub hp).differentiableOn.mul
    (differentiableOn_intervalIntegral_of_continuousOn hW ?_ ?_)
  · rintro ⟨z, τ⟩ ⟨hz, hτ⟩
    obtain ⟨hA, hB⟩ := hpos z hz τ hτ
    refine ContinuousAt.continuousWithinAt ?_
    show ContinuousAt (fun x : ℂ × ℝ => Gamma (1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1)) * v) *
      Gamma (1 - (x.1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1))) * v)) (z, τ)
    refine ContinuousAt.mul ?_ ?_
    · exact (gamma_differentiableAt hA).continuousAt.comp
        (f := fun x : ℂ × ℝ => 1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1)) * v)
        (by fun_prop)
    · exact (gamma_differentiableAt hB).continuousAt.comp
        (f := fun x : ℂ × ℝ => 1 - (x.1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1))) * v)
        (by fun_prop)
  · intro τ hτ z hz
    obtain ⟨hA, hB⟩ := hpos z hz τ hτ
    have hpz := hp z
    have hqz := hq z
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ ?_
    · exact (gamma_differentiableAt hA).comp z
        (f := fun z => 1 - (p z + (τ : ℂ) * (q z - p z)) * v) (by fun_prop)
    · exact (gamma_differentiableAt hB).comp z
        (f := fun z => 1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v) (by fun_prop)

/-- `segInt` between real endpoints is the real interval integral. -/
theorem segInt_ofReal (g : ℂ → ℂ) (x y : ℝ) :
    segInt g x y = ∫ u in x..y, g u := by
  unfold segInt
  have := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun u : ℝ => g u) (y - x) x
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at this
  rw [← this, Complex.real_smul]
  push_cast
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  ring_nf

theorem phiD_eq_left (κ : ℝ) {b w : ℝ} (hw : w ∈ Icc (0 : ℝ) (1 - b)) :
    phiD κ b w = segInt (kG (slantDir κ) w) 0 w := by
  unfold phiD
  rw [max_eq_left (by linarith [hw.2]), min_eq_left hw.2,
    show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, segInt_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [kG]
  push_cast
  ring_nf

theorem phiD_eq_right (κ : ℝ) {b w : ℝ} (hw : w ∈ Icc (1 - b) (2 * (1 - b))) :
    phiD κ b w = segInt (kG (slantDir κ) w) (w - ((1 - b : ℝ) : ℂ)) ((1 - b : ℝ) : ℂ) := by
  unfold phiD
  rw [max_eq_right (by linarith [hw.1]), min_eq_right hw.1,
    show (w : ℂ) - ((1 - b : ℝ) : ℂ) = ((w - (1 - b) : ℝ) : ℂ) by push_cast; ring, segInt_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [kG]
  push_cast
  ring_nf

/-- An integral `∫_x^y h(w)/(δ - t₀ + w) dw` over an interval at distance `≥ η` from `t₀` is
holomorphic in `δ` for `|δ| < η/2`. -/
theorem piece_analytic {h : ℝ → ℂ} {x y t₀ η : ℝ} (hxy : x ≤ y)
    (hh : ContinuousOn h (Icc x y)) (hfar : ∀ w ∈ Icc x y, η ≤ |w - t₀|) :
    AnalyticOnNhd ℂ (fun δ : ℂ => ∫ w in x..y, h w / (δ - t₀ + w)) (ball 0 (η / 2)) := by
  have hden : ∀ δ ∈ ball (0 : ℂ) (η / 2), ∀ w ∈ Icc x y, δ - t₀ + w ≠ 0 := by
    intro δ hδ w hw h0
    have : δ = ((t₀ - w : ℝ) : ℂ) := by push_cast; linear_combination h0
    rw [mem_ball_zero_iff, this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hδ
    have := hfar w hw
    have : 0 ≤ |w - t₀| := abs_nonneg _
    linarith
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
  refine differentiableOn_intervalIntegral_of_continuousOn isOpen_ball ?_ ?_
  · rw [uIcc_of_le hxy]
    show ContinuousOn (fun p : ℂ × ℝ => h p.2 / (p.1 - t₀ + p.2)) _
    refine ContinuousOn.div (hh.comp continuousOn_snd fun p hp => hp.2) (by fun_prop) ?_
    rintro ⟨δ, w⟩ ⟨hδ, hw⟩
    exact hden δ hδ w hw
  · intro w hw
    rw [uIcc_of_le hxy] at hw
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) ?_
    intro δ hδ
    exact hden δ hδ w hw

/-- The core: continuation across of `δ ↦ ∫_x^y h(w)/(δ - t₀ + w) dw` from `Im δ > 0`, when `h` is
continuous and agrees near `t₀` with a holomorphic `g`. -/
theorem access_core {h : ℝ → ℂ} {g : ℂ → ℂ} {x y t₀ η R : ℝ} (hη : 0 < η) (hηR : η < R)
    (hx : x ≤ t₀ - η) (hy : t₀ + η ≤ y)
    (hh₁ : ContinuousOn h (Icc x (t₀ - η))) (hh₃ : ContinuousOn h (Icc (t₀ + η) y))
    (hg : DifferentiableOn ℂ g (ball (t₀ : ℂ) R))
    (hhg : ∀ w ∈ Icc (t₀ - η) (t₀ + η), h w = g w) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 (η / 2)) ∧
      ∀ δ ∈ ball (0 : ℂ) (η / 2), 0 < δ.im → F δ = ∫ w in x..y, h w / (δ - t₀ + w) := by
  have hI₁ := piece_analytic (t₀ := t₀) (η := η) hx hh₁ fun w hw => by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hw.2])]; linarith [hw.2]
  have hI₃ := piece_analytic (t₀ := t₀) (η := η) hy hh₃ fun w hw => by
    rw [abs_of_nonneg (by linarith [hw.1])]; linarith [hw.1]
  have hgR : ∀ u : ℝ, |u| ≤ η → ((u : ℂ) + t₀) ∈ ball (t₀ : ℂ) R := by
    intro u hu
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs]
    linarith
  obtain ⟨F₀, hF₀, hF₀eq⟩ := cauchyInt (f := fun z => g (z + t₀)) (ρ := η / 2) (w₁ := -η)
    (w₂ := η) (by positivity) (by linarith) (by linarith) (U := ball 0 R) isOpen_ball
    (convex_ball 0 R) (ball_subset_ball (by linarith))
    (fun u hu => by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_le_of_lt (abs_le.mpr ⟨hu.1, hu.2⟩) hηR)
    (hg.comp (differentiableOn_id.add_const _) fun z hz => by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]; exact hz)
  refine ⟨fun δ => (∫ w in x..(t₀ - η), h w / (δ - t₀ + w)) + F₀ δ +
    ∫ w in (t₀ + η)..y, h w / (δ - t₀ + w), (hI₁.add hF₀).add hI₃, fun δ hδ hδim => ?_⟩
  have hden : ∀ w : ℝ, δ - t₀ + w ≠ 0 := by
    intro w h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hgc : ContinuousOn (fun w : ℝ => g w) (Icc (t₀ - η) (t₀ + η)) := by
    refine hg.continuousOn.comp Complex.continuous_ofReal.continuousOn fun w hw => ?_
    have := hgR (w - t₀) (abs_le.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩)
    push_cast at this
    simpa using this
  have hdc : Continuous fun w : ℝ => δ - t₀ + w := by fun_prop
  have i₁ : IntervalIntegrable (fun w : ℝ => h w / (δ - t₀ + w)) volume x (t₀ - η) :=
    (hh₁.div hdc.continuousOn fun w _ => hden w).intervalIntegrable_of_Icc hx
  have i₃ : IntervalIntegrable (fun w : ℝ => h w / (δ - t₀ + w)) volume (t₀ + η) y :=
    (hh₃.div hdc.continuousOn fun w _ => hden w).intervalIntegrable_of_Icc hy
  have hmid : EqOn (fun w : ℝ => h w / (δ - t₀ + w)) (fun w : ℝ => g w / (δ - t₀ + w))
      (uIcc (t₀ - η) (t₀ + η)) := by
    intro w hw
    rw [uIcc_of_le (by linarith)] at hw
    simp only [hhg w hw]
  have i₂ : IntervalIntegrable (fun w : ℝ => h w / (δ - t₀ + w)) volume (t₀ - η) (t₀ + η) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.congr ?_ hmid
    rw [uIcc_of_le (by linarith)]
    exact hgc.div hdc.continuousOn fun w _ => hden w
  rw [← intervalIntegral.integral_add_adjacent_intervals i₁ (i₂.trans i₃),
    ← intervalIntegral.integral_add_adjacent_intervals i₂ i₃, ← add_assoc]
  beta_reduce
  congr 2
  rw [hF₀eq δ hδ hδim, intervalIntegral.integral_congr hmid]
  have := intervalIntegral.integral_comp_add_right (a := -η) (b := η)
    (fun w : ℝ => g w / (δ - t₀ + w)) t₀
  rw [show -η + t₀ = t₀ - η by ring, show η + t₀ = t₀ + η by ring] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast
  ring_nf

theorem phiD_continuousOn (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun w : ℝ => phiD κ b w) (Icc 0 (2 * (1 - b))) := by
  set v := slantDir κ with hv
  have hvre : v.re = 1 := by simp [hv, slantDir]
  have hcre : ∀ x : ℝ, ((x : ℂ) * v).re = x := by intro x; simp [hvre]
  have hb1 : 1 - b < 1 := by linarith [hb.1]
  have hf₁ : DifferentiableOn ℂ (fun z => segInt (kG v z) ((fun _ => (0 : ℂ)) z) ((fun z => z) z))
      {z : ℂ | (z * v).re < 1} :=
    segGamma_differentiableOn (p := fun _ => (0 : ℂ)) (q := fun z => z) (differentiable_const _)
      differentiable_id (isOpen_lt (by fun_prop) continuous_const) (fun z _ => by simp)
      (fun z hz => hz) (fun z hz => by show ((z - 0) * v).re < 1; rw [sub_zero]; exact hz)
      (fun z _ => by simp)
  have hf₂ : DifferentiableOn ℂ
      (fun z => segInt (kG v z) ((fun z => z - ((1 - b : ℝ) : ℂ)) z) ((fun _ => ((1 - b : ℝ) : ℂ)) z))
      {z : ℂ | ((z - ((1 - b : ℝ) : ℂ)) * v).re < 1} :=
    segGamma_differentiableOn (p := fun z => z - ((1 - b : ℝ) : ℂ)) (q := fun _ => ((1 - b : ℝ) : ℂ))
      (differentiable_id.sub_const _) (differentiable_const _)
      (isOpen_lt (by fun_prop) continuous_const) (fun z hz => hz)
      (fun z _ => by show (((1 - b : ℝ) : ℂ) * v).re < 1; rw [hcre]; exact hb1)
      (fun z _ => by
        show ((z - (z - ((1 - b : ℝ) : ℂ))) * v).re < 1
        rw [sub_sub_cancel, hcre]; exact hb1)
      (fun z hz => hz)
  have hL : ContinuousOn (fun w : ℝ => phiD κ b w) (Icc 0 (1 - b)) := by
    refine ContinuousOn.congr (f := fun w : ℝ => segInt (kG v w) 0 w) ?_
      (fun w hw => phiD_eq_left κ hw)
    refine hf₁.continuousOn.comp Complex.continuous_ofReal.continuousOn fun w hw => ?_
    show ((w : ℂ) * v).re < 1
    rw [hcre]; linarith [hw.2]
  have hR : ContinuousOn (fun w : ℝ => phiD κ b w) (Icc (1 - b) (2 * (1 - b))) := by
    refine ContinuousOn.congr
      (f := fun w : ℝ => segInt (kG v w) ((w : ℂ) - ((1 - b : ℝ) : ℂ)) ((1 - b : ℝ) : ℂ)) ?_
      (fun w hw => phiD_eq_right κ hw)
    refine hf₂.continuousOn.comp Complex.continuous_ofReal.continuousOn fun w hw => ?_
    show (((w : ℂ) - ((1 - b : ℝ) : ℂ)) * v).re < 1
    rw [show (w : ℂ) - ((1 - b : ℝ) : ℂ) = ((w - (1 - b) : ℝ) : ℂ) by push_cast; ring, hcre]
    linarith [hw.2]
  have := hL.union_of_isClosed hR isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by linarith [hb.2]) (by linarith [hb.2])] at this

end DcAccessTwo

open DcAccessTwo in
/-- **`𝒟` across `cut_2`** (the access lemma(ii),(iii) for `𝒟`; the kink of `φ` at `w = 1-b` is
avoided by `t₀ ≠ 1-b`). No RH.

Sketch. `Dc_eq_diag` (upper-side points are off `𝒮 + 𝒮`); with `(s-2)/v = δ - t₀`, the singular
point is `w = t₀ - δ`. `phiD` is holomorphic near `t₀` (formula `∫_0^w` if `t₀ < 1-b`, `∫_{w-(1-b)}^{1-b}`
if `t₀ > 1-b`, extended as `segInt`); split off a small interval around `t₀` and apply `cauchyInt`
there; the rest is holomorphic. -/
theorem Dc_access_two (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) (2 * (1 - b))) (hne : t₀ ≠ 1 - b) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball (2 - (t₀ : ℂ) * slantDir κ) r) ∧
      ∀ s ∈ ball (2 - (t₀ : ℂ) * slantDir κ) r,
        0 < ((s - (2 - (t₀ : ℂ) * slantDir κ)) / slantDir κ).im → F s = Dc κ b s := by
  set v := slantDir κ with hv
  have hv0 : v ≠ 0 := slantDir_ne_zero κ
  have hvre : v.re = 1 := by simp [hv, slantDir]
  have hcre : ∀ x : ℝ, ((x : ℂ) * v).re = x := by intro x; simp [hvre]
  have hb1 : 1 - b < 1 := by linarith [hb.1]
  have hb0 : 0 < 1 - b := by linarith [hb.2]
  have hcont := phiD_continuousOn κ hb
  have ht01 := ht₀.1
  have ht02 := ht₀.2
  obtain ⟨g, η, R, hη, hηR, hx, hy, hg, hhg⟩ : ∃ g : ℂ → ℂ, ∃ η R : ℝ, 0 < η ∧ η < R ∧
      0 ≤ t₀ - η ∧ t₀ + η ≤ 2 * (1 - b) ∧ DifferentiableOn ℂ g (ball (t₀ : ℂ) R) ∧
      ∀ w ∈ Icc (t₀ - η) (t₀ + η), phiD κ b w = g w := by
    rcases lt_or_gt_of_ne hne with h | h
    · -- `t₀ < 1 - b`: left formula
      set W : Set ℂ := {z : ℂ | (z * v).re < 1} with hW
      have hWo : IsOpen W := isOpen_lt (by fun_prop) continuous_const
      have hf₁ : DifferentiableOn ℂ
          (fun z => segInt (kG v z) ((fun _ => (0 : ℂ)) z) ((fun z => z) z)) W :=
        segGamma_differentiableOn (p := fun _ => (0 : ℂ)) (q := fun z => z)
          (differentiable_const _) differentiable_id hWo
          (fun z _ => by simp) (fun z hz => hz)
          (fun z hz => by show ((z - 0) * v).re < 1; rw [sub_zero]; exact hz)
          (fun z _ => by simp)
      have ht : (t₀ : ℂ) ∈ W := by
        show ((t₀ : ℂ) * v).re < 1
        rw [hcre]; linarith
      obtain ⟨R₀, hR₀, hR₀W⟩ := Metric.isOpen_iff.mp hWo _ ht
      refine ⟨_, min (R₀ / 2) (min (t₀ / 2) ((1 - b - t₀) / 2)), R₀, ?_, ?_, ?_, ?_,
        hf₁.mono hR₀W, fun w hw => ?_⟩
      · have := ht₀.1
        exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · linarith [min_le_left (t₀ / 2) ((1 - b - t₀) / 2),
          min_le_right (R₀ / 2) (min (t₀ / 2) ((1 - b - t₀) / 2))]
      · linarith [min_le_right (t₀ / 2) ((1 - b - t₀) / 2),
          min_le_right (R₀ / 2) (min (t₀ / 2) ((1 - b - t₀) / 2))]
      · have h1 := min_le_left (t₀ / 2) ((1 - b - t₀) / 2)
        have h2 := min_le_right (t₀ / 2) ((1 - b - t₀) / 2)
        have h3 := min_le_right (R₀ / 2) (min (t₀ / 2) ((1 - b - t₀) / 2))
        exact phiD_eq_left κ ⟨by linarith [hw.1], by linarith [hw.2]⟩
    · -- `t₀ > 1 - b`: right formula
      set W : Set ℂ := {z : ℂ | ((z - ((1 - b : ℝ) : ℂ)) * v).re < 1} with hW
      have hWo : IsOpen W := isOpen_lt (by fun_prop) continuous_const
      have hf₂ : DifferentiableOn ℂ
          (fun z => segInt (kG v z) ((fun z => z - ((1 - b : ℝ) : ℂ)) z)
            ((fun _ => ((1 - b : ℝ) : ℂ)) z)) W :=
        segGamma_differentiableOn (p := fun z => z - ((1 - b : ℝ) : ℂ))
          (q := fun _ => ((1 - b : ℝ) : ℂ)) (differentiable_id.sub_const _)
          (differentiable_const _) hWo (fun z hz => hz)
          (fun z _ => by show (((1 - b : ℝ) : ℂ) * v).re < 1; rw [hcre]; exact hb1)
          (fun z _ => by
            show ((z - (z - ((1 - b : ℝ) : ℂ))) * v).re < 1
            rw [sub_sub_cancel, hcre]; exact hb1) (fun z hz => hz)
      have ht : (t₀ : ℂ) ∈ W := by
        show (((t₀ : ℂ) - ((1 - b : ℝ) : ℂ)) * v).re < 1
        rw [show (t₀ : ℂ) - ((1 - b : ℝ) : ℂ) = ((t₀ - (1 - b) : ℝ) : ℂ) by push_cast; ring,
          hcre]
        linarith [ht₀.2]
      obtain ⟨R₀, hR₀, hR₀W⟩ := Metric.isOpen_iff.mp hWo _ ht
      refine ⟨_, min (R₀ / 2) (min ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2)), R₀, ?_, ?_,
        ?_, ?_, hf₂.mono hR₀W, fun w hw => ?_⟩
      · have := ht₀.2
        exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · linarith [min_le_left ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2),
          min_le_right (R₀ / 2) (min ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2))]
      · linarith [min_le_right ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2),
          min_le_right (R₀ / 2) (min ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2))]
      · have h1 := min_le_left ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2)
        have h2 := min_le_right ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2)
        have h3 := min_le_right (R₀ / 2) (min ((t₀ - (1 - b)) / 2) ((2 * (1 - b) - t₀) / 2))
        exact phiD_eq_right κ ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨F₀, hF₀, hF₀eq⟩ := access_core (h := fun w => phiD κ b w) hη hηR hx hy
    (hcont.mono (Icc_subset_Icc le_rfl (by linarith)))
    (hcont.mono (Icc_subset_Icc (by linarith) le_rfl)) hg hhg
  have hvn : 1 ≤ ‖v‖ := by
    have := Complex.abs_re_le_norm v
    rw [hvre, abs_one] at this
    exact this
  have hδball : ∀ s ∈ ball (2 - (t₀ : ℂ) * v) (η / 2),
      (s - (2 - (t₀ : ℂ) * v)) / v ∈ ball (0 : ℂ) (η / 2) := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    rw [mem_ball_zero_iff, norm_div]
    calc ‖s - (2 - (t₀ : ℂ) * v)‖ / ‖v‖ ≤ ‖s - (2 - (t₀ : ℂ) * v)‖ :=
          div_le_self (norm_nonneg _) hvn
      _ < η / 2 := hs
  refine ⟨η / 2, by positivity, fun s => v * F₀ ((s - (2 - (t₀ : ℂ) * v)) / v), ?_, ?_⟩
  · intro s hs
    refine analyticAt_const.mul ?_
    exact (hF₀ _ (hδball s hs)).comp (f := fun s => (s - (2 - (t₀ : ℂ) * v)) / v) (by fun_prop)
  · intro s hs hsim
    have hsS : s ∉ segSS κ b := by
      rintro ⟨w, -, rfl⟩
      have e : ((2 - (w : ℂ) * v) - (2 - (t₀ : ℂ) * v)) / v = ((t₀ - w : ℝ) : ℂ) := by
        field_simp; push_cast; ring
      rw [e, Complex.ofReal_im] at hsim
      exact lt_irrefl _ hsim
    show v * F₀ ((s - (2 - (t₀ : ℂ) * v)) / v) = _
    rw [Dc_eq_diag κ hb hsS, hF₀eq _ (hδball s hs) hsim, ← hv]
    congr 1
    refine intervalIntegral.integral_congr fun w _ => ?_
    congr 1
    field_simp
    ring

end GoldbachBoundaries.ThmA
