import PrimePairNB.HInf.Fill.isOpen_Uth
import PrimePairNB.HInf.Fill.add_mem_Uth

/-! Proofs of `hasDerivAt_Pth` and `Pth_eq_P`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma re_add_mul_slantDir (κ : ℝ) (z : ℂ) (t : ℝ) : (z + (t : ℂ) * slantDir κ).re = z.re + t := by
  simp [slantDir]

lemma im_add_mul_slantDir (κ : ℝ) (z : ℂ) (t : ℝ) : (z + (t : ℂ) * slantDir κ).im = z.im + t * κ := by
  simp [slantDir]

/-- `U_θ ⊆ {Re z > 0} ∖ Σ`: `a ∈ Σ` lies on its own ray. -/
lemma Uth_subset (κ : ℝ) : Uth κ ⊆ halfPlane 0 \ PoleSetQ := by
  intro z hz
  refine ⟨hz.1, fun hzP => hz.2 ?_⟩
  exact mem_iUnion₂.mpr ⟨z, hzP, 0, le_rfl, by simp⟩

/-- `P^θ` is a primitive of `-Q` on `U_θ`. -/
theorem hasDerivAt_Pth {κ : ℝ} {z : ℂ} (hz : z ∈ Uth κ) : HasDerivAt (Pth κ) (-Qcont z) z := by
  have hz0 : 0 < z.re := hz.1
  set w : ℂ := slantDir κ with hw
  set K : Set ℂ := segment ℝ z (z + 2 * w) with hK
  have hKU : K ⊆ Uth κ := by
    rintro u ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have hu : a • z + b • (z + 2 * w) = z + ((2 * b : ℝ) : ℂ) * w := by
      simp only [Complex.real_smul]
      push_cast
      linear_combination z * hab'
    rw [hu]
    exact add_mem_Uth hz (by positivity)
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 2 → z + (t : ℂ) * w ∈ K := fun t ht =>
    ⟨1 - t / 2, t / 2, by linarith [ht.2], by linarith [ht.1], by ring, by
      simp only [Complex.real_smul]
      push_cast
      ring⟩
  have hKc : IsCompact K := by
    rw [hK, segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨ε, hε, hεK⟩ := hKc.exists_thickening_subset_open (isOpen_Uth κ) hKU
  set U : Set ℂ := thickening ε K with hU
  have hUo : IsOpen U := isOpen_thickening
  have hUc : Convex ℝ U := (convex_segment z (z + 2 * w)).thickening ε
  have hzU : z ∈ U := self_subset_thickening hε K (left_mem_segment ℝ z (z + 2 * w))
  have hQd : DifferentiableOn ℂ Qcont U := fun u hu =>
    (M2.isQCont_Qcont.2.2 u (Uth_subset κ (hεK hu))).differentiableAt.differentiableWithinAt
  set Φ : ℂ → ℂ := fun u => ThmA.segInt Qcont z u with hΦdef
  have hΦ : ∀ u ∈ U, HasDerivAt Φ (Qcont u) u := fun u hu =>
    ThmA.GroupDPrimitive.hasDerivAt_segInt hUo hUc hQd hzU hu
  have hshift : ∀ v ∈ ball z ε, ∀ t ∈ Icc (0 : ℝ) 2, v + (t : ℂ) * w ∈ U := by
    intro v hv t ht
    rw [hU, mem_thickening_iff]
    refine ⟨z + (t : ℂ) * w, hseg t ht, ?_⟩
    rw [dist_eq_norm, add_sub_add_right_eq_sub, ← dist_eq_norm]
    exact hv
  have hint : ∀ v ∈ ball z ε,
      w * (∫ t in (0 : ℝ)..2, Qcont (v + (t : ℂ) * w)) = Φ (v + 2 * w) - Φ v := by
    intro v hv
    have hd : ∀ t ∈ uIcc (0 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Φ (v + (t : ℂ) * w)) (w * Qcont (v + (t : ℂ) * w)) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have h0 : HasDerivAt (fun x : ℂ => v + x * w) w (t : ℂ) := by
        simpa using ((hasDerivAt_id (t : ℂ)).mul_const w).const_add v
      have h1 : HasDerivAt (fun x : ℂ => Φ (v + x * w)) (w * Qcont (v + (t : ℂ) * w)) (t : ℂ) := by
        have := HasDerivAt.comp (t : ℂ) (h₂ := Φ) (h := fun x : ℂ => v + x * w)
          (hΦ (v + (t : ℂ) * w) (hshift v hv t ht)) h0
        simpa [Function.comp_def, mul_comm] using this
      exact h1.comp_ofReal
    have hc : ContinuousOn (fun t : ℝ => w * Qcont (v + (t : ℂ) * w)) (uIcc 0 2) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hc' : ContinuousAt (fun t : ℝ => Qcont (v + (t : ℂ) * w)) t :=
        ContinuousAt.comp (f := fun t : ℝ => v + (t : ℂ) * w) (g := Qcont)
          (hQd.differentiableAt (hUo.mem_nhds (hshift v hv t ht))).continuousAt (by fun_prop)
      exact (continuousAt_const.mul hc').continuousWithinAt
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    rw [intervalIntegral.integral_const_mul] at this
    simpa using this
  have hev : (fun v => w * ∫ t in (0 : ℝ)..2, Qcont (v + (t : ℂ) * w)) =ᶠ[𝓝 z]
      fun v => Φ (v + 2 * w) - Φ v :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds z hε) hint
  have hz2U : z + 2 * w ∈ U := by
    simpa using hshift z (mem_ball_self hε) 2 ⟨by norm_num, le_rfl⟩
  have hD1 : HasDerivAt (fun v => Φ (v + 2 * w) - Φ v) (Qcont (z + 2 * w) - Qcont z) z := by
    have h1 : HasDerivAt (fun v => Φ (v + 2 * w)) (Qcont (z + 2 * w)) z := by
      have := (hΦ (z + 2 * w) hz2U).comp z ((hasDerivAt_id z).add_const (2 * w))
      simpa [Function.comp_def] using this
    exact h1.sub (hΦ z hzU)
  have hD2 : HasDerivAt (fun v => w * ∫ t in (0 : ℝ)..2, Qcont (v + (t : ℂ) * w))
      (Qcont (z + 2 * w) - Qcont z) z := hD1.congr_of_eventuallyEq hev
  have hre2 : 1 < (z + 2 * w).re := by
    have := re_add_mul_slantDir κ z 2
    simp only [ofReal_ofNat] at this
    rw [hw, this]
    linarith
  have hP : HasDerivAt (fun v => P (v + 2 * w)) (-Q (z + 2 * w)) z := by
    have := (hasDerivAt_P (show z + 2 * w ∈ halfPlane 1 from hre2)).comp z
      ((hasDerivAt_id z).add_const (2 * w))
    simpa [Function.comp_def] using this
  have hsum := hP.add hD2
  have heq : -Qcont z = -Q (z + 2 * w) + (Qcont (z + 2 * w) - Qcont z) := by
    rw [TIdentity.Qcont_eq_Q_of_one_lt hre2]
    ring
  rw [heq]
  exact hsum

/-- `P^θ = P` on `Re z > 1`. -/
theorem Pth_eq_P (κ : ℝ) {z : ℂ} (hz : 1 < z.re) : Pth κ z = P z := by
  set w : ℂ := slantDir κ with hw
  have hre : ∀ t : ℝ, 0 ≤ t → 1 < (z + (t : ℂ) * w).re := fun t ht => by
    rw [hw, re_add_mul_slantDir]
    linarith
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 2,
      HasDerivAt (fun t : ℝ => P (z + (t : ℂ) * w)) (-(w * Qcont (z + (t : ℂ) * w))) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h0 : HasDerivAt (fun x : ℂ => z + x * w) w (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const w).const_add z
    have h1 : HasDerivAt (fun x : ℂ => P (z + x * w)) (-(w * Q (z + (t : ℂ) * w))) (t : ℂ) := by
      have := HasDerivAt.comp (t : ℂ) (h₂ := P) (h := fun x : ℂ => z + x * w)
        (hasDerivAt_P (show z + (t : ℂ) * w ∈ halfPlane 1 from hre t ht.1)) h0
      have e : -(w * Q (z + (t : ℂ) * w)) = -Q (z + (t : ℂ) * w) * w := by ring
      rw [e]
      exact this
    rw [TIdentity.Qcont_eq_Q_of_one_lt (hre t ht.1)]
    exact h1.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => -(w * Qcont (z + (t : ℂ) * w))) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have hc : ContinuousAt (fun t : ℝ => Qcont (z + (t : ℂ) * w)) t :=
      ContinuousAt.comp (f := fun t : ℝ => z + (t : ℂ) * w) (g := Qcont)
        (TIdentity.analyticAt_Qcont_of_one_lt (hre t ht.1)).continuousAt (by fun_prop)
    exact (continuousAt_const.mul hc).neg.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hftc
  simp only [ofReal_ofNat, ofReal_zero, zero_mul, add_zero] at hftc
  show P (z + 2 * w) + w * _ = P z
  linear_combination -hftc

end GoldbachBoundaries.HInf.Fill
