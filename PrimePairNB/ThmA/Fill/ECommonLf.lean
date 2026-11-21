import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

/-!
# shared facts about `L(t) = ∫_𝒮 Γ(x) t^{-x} dx` and `Y`

Helpers live in the namespace `GoldbachBoundaries.ThmA.GroupE`.

Throughout `x_u = 1 - u v`, `u ∈ [0, 1-b]`, `Re x_u = 1 - u ∈ [b, 1]`.

* `continuousOn_Lf`, `norm_Lf_le`: `L` is continuous on `t > 0` and `|L(t)| ≤ K t^{-1}` on `(0, 1]`.
* `integral_Lf_mul`: Fubini, `∫_0^1 L(t) g(t) t^{s-1} dt = v ∫_0^{1-b} Γ(x_u) ∫_0^1 g(t) t^{(s - x_u) - 1} dt du`
  for `|g(t)| ≤ C t^{-a}` on `(0, 1]` and `Re s > 1 + a`.
* `integral_Lf_cpow`: `∫_0^1 L(t) t^{z-1} dt = Y(z)` for `Re z > 1`.
* `analyticOnNhd_Yf`: `Y` is holomorphic off `𝒮`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-! ### Helpers (prefix `lf_`) -/

theorem lf_re (κ u : ℝ) : (1 - (u : ℂ) * slantDir κ).re = 1 - u := by
  simp [slantDir]

theorem lf_continuousAt_Gamma {κ u : ℝ} (hu : u < 1) :
    ContinuousAt (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ)) u := by
  have h : 0 < (1 - (u : ℂ) * slantDir κ).re := by rw [lf_re]; linarith
  have hc : ContinuousAt (fun u : ℝ => 1 - (u : ℂ) * slantDir κ) u := by fun_prop
  exact ContinuousAt.comp (g := Gamma) (f := fun u : ℝ => 1 - (u : ℂ) * slantDir κ)
    (TIdentity.differentiableAt_Gamma_of_re_pos h).continuousAt hc

theorem lf_continuousOn_Gamma {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ)) (Icc 0 (1 - b)) :=
  fun _ hu => (lf_continuousAt_Gamma (by linarith [hu.2, hb.1])).continuousWithinAt

theorem lf_Gamma_bound {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (0 : ℝ) (1 - b), ‖Gamma (1 - (u : ℂ) * slantDir κ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (lf_continuousOn_Gamma (κ := κ) hb)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1 - b) := ⟨le_rfl, by linarith [hb.2]⟩
  exact ⟨M, (norm_nonneg _).trans (hM 0 h0), hM⟩

theorem lf_norm_cpow_le {κ u t : ℝ} (hu : 0 ≤ u) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖(t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ))‖ ≤ t ^ (-1 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.neg_re, lf_re]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)

theorem lf_cpow_mul {κ u t : ℝ} (ht : 0 < t) (s : ℂ) :
    (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ)) * (t : ℂ) ^ (s - 1) =
      (t : ℂ) ^ (s - 1 + (u : ℂ) * slantDir κ - 1) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
  congr 1
  ring

/-! ### Main statements -/

theorem continuousOn_Lf {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) : ContinuousOn (Lf κ b) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  refine ContinuousAt.continuousWithinAt ?_
  -- clamp `u` to `[0, 1-b]` and `t` to `[t₀/2, ∞)`
  set c : ℝ → ℝ := fun u => max 0 (min u (1 - b)) with hc
  have hcc : Continuous c := by fun_prop
  have hcmem : ∀ u, c u ∈ Icc (0 : ℝ) (1 - b) := fun u =>
    ⟨le_max_left _ _, max_le (by linarith [hb.2]) (min_le_right _ _)⟩
  set G : ℝ → ℝ → ℂ := fun t u => Gamma (1 - ((c u : ℝ) : ℂ) * slantDir κ) *
    (((max t (t₀ / 2) : ℝ)) : ℂ) ^ (-(1 - ((c u : ℝ) : ℂ) * slantDir κ)) with hG
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun p : ℝ × ℝ => Gamma (1 - ((c p.2 : ℝ) : ℂ) * slantDir κ) := by
      have : Continuous fun p : ℝ × ℝ => c p.2 := hcc.comp continuous_snd
      refine continuous_iff_continuousAt.2 fun p => ?_
      have hlt : c p.2 < 1 := by linarith [(hcmem p.2).2, hb.1]
      exact ContinuousAt.comp (g := fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ))
        (f := fun p : ℝ × ℝ => c p.2) (lf_continuousAt_Gamma (κ := κ) hlt) this.continuousAt
    have h2 : Continuous fun p : ℝ × ℝ =>
        (((max p.1 (t₀ / 2) : ℝ)) : ℂ) ^ (-(1 - ((c p.2 : ℝ) : ℂ) * slantDir κ)) := by
      refine Continuous.cpow (by fun_prop) (by fun_prop) fun p => ?_
      exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le (by linarith) (le_max_right _ _))
    exact h1.mul h2
  have hcont : Continuous fun t => slantDir κ * ∫ u in (0 : ℝ)..(1 - b), G t u :=
    continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc _ _)
  refine hcont.continuousAt.congr ?_
  filter_upwards [lt_mem_nhds (show t₀ / 2 < t₀ by linarith)] with t ht
  simp only [Lf]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (by linarith [hb.2])] at hu
  have hcu : c u = u := by
    simp only [hc]; rw [min_eq_left hu.2, max_eq_right hu.1]
  simp only [hG, hcu, max_eq_left ht.le]

theorem norm_Lf_le {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ K : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Lf κ b t‖ ≤ K * t ^ (-1 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := lf_Gamma_bound (κ := κ) hb
  refine ⟨‖slantDir κ‖ * (M * |1 - b - 0|), fun t ht => ?_⟩
  have h1b : (0 : ℝ) ≤ 1 - b := by linarith [hb.2]
  have hI : ‖∫ u in (0 : ℝ)..(1 - b),
      Gamma (1 - (u : ℂ) * slantDir κ) * (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ))‖ ≤
        M * t ^ (-1 : ℝ) * |1 - b - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le h1b] at hu
    rw [norm_mul]
    exact mul_le_mul (hM u ⟨hu.1.le, hu.2⟩) (lf_norm_cpow_le hu.1.le ht) (norm_nonneg _) hM0
  rw [Lf, norm_mul]
  calc ‖slantDir κ‖ * ‖∫ u in (0 : ℝ)..(1 - b),
        Gamma (1 - (u : ℂ) * slantDir κ) * (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ))‖
      ≤ ‖slantDir κ‖ * (M * t ^ (-1 : ℝ) * |1 - b - 0|) :=
        mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = ‖slantDir κ‖ * (M * |1 - b - 0|) * t ^ (-1 : ℝ) := by ring

theorem integral_Lf_mul {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {g : ℝ → ℂ} {a C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1)))
    (hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ (-a)) {s : ℂ} (hs : 1 + a < s.re) :
    IntegrableOn (fun t : ℝ => Lf κ b t * g t * (t : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, Lf κ b t * g t * (t : ℂ) ^ (s - 1) =
        slantDir κ * ∫ u in (0 : ℝ)..(1 - b), Gamma (1 - (u : ℂ) * slantDir κ) *
          ∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (s - 1 + (u : ℂ) * slantDir κ - 1) := by
  have h1b : (0 : ℝ) ≤ 1 - b := by linarith [hb.2]
  obtain ⟨M, hM0, hM⟩ := lf_Gamma_bound (κ := κ) hb
  have hC : 0 ≤ C := by
    have := hbound 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 - b)) with hν
  set F : ℝ → ℝ → ℂ := fun t u => Gamma (1 - (u : ℂ) * slantDir κ) *
    (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ)) * g t * (t : ℂ) ^ (s - 1) with hF
  -- measurability
  have hA : ContinuousOn (fun p : ℝ × ℝ => Gamma (1 - (p.2 : ℂ) * slantDir κ) *
      (p.1 : ℂ) ^ (-(1 - (p.2 : ℂ) * slantDir κ)) * (p.1 : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) (1 - b)) := by
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    have hp1 : (p.1 : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 hp.1.1
    have hG : ContinuousAt (fun p : ℝ × ℝ => Gamma (1 - (p.2 : ℂ) * slantDir κ)) p :=
      (lf_continuousAt_Gamma (κ := κ) (by linarith [hp.2.2, hb.1])).comp continuous_snd.continuousAt
    refine (hG.mul ?_).mul ?_
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) hp1
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) hp1
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Gamma (1 - (p.2 : ℂ) * slantDir κ) *
        (p.1 : ℂ) ^ (-(1 - (p.2 : ℂ) * slantDir κ)) * (p.1 : ℂ) ^ (s - 1)) (μ.prod ν) := by
      rw [hμ, hν, Measure.prod_restrict]
      exact hA.aestronglyMeasurable (measurableSet_Ioc.prod measurableSet_Ioc)
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1) (μ.prod ν) := hg.comp_fst
    refine (h1.mul h2).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, Function.uncurry, hF]
    ring
  -- domination
  have hr : -1 < s.re - 2 - a := by linarith
  have hBint : Integrable (fun t : ℝ => M * C * t ^ (s.re - 2 - a)) μ := by
    refine Integrable.const_mul ?_ _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  have hInt : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine Integrable.mono' (hBint.comp_fst ν) hmeas ?_
    rw [hμ, hν, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
      (Eventually.of_forall fun p hp => ?_)
    obtain ⟨t, u⟩ := p
    obtain ⟨ht, hu⟩ := hp
    simp only [Function.uncurry, hF, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1 (s - 1)]
    have e : t ^ (s.re - 2 - a) = t ^ (-1 : ℝ) * t ^ (-a) * t ^ (s - 1).re := by
      rw [← Real.rpow_add ht.1, ← Real.rpow_add ht.1]
      congr 1
      simp
      ring
    rw [e]
    have hg' := hbound t ht
    have hc' := lf_norm_cpow_le (κ := κ) hu.1.le ht
    have hG' := hM u ⟨hu.1.le, hu.2⟩
    have hp1 : 0 ≤ t ^ (-1 : ℝ) := Real.rpow_nonneg ht.1.le _
    have hp2 : 0 ≤ t ^ (s - 1).re := Real.rpow_nonneg ht.1.le _
    calc ‖Gamma (1 - (u : ℂ) * slantDir κ)‖ * ‖(t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ))‖ * ‖g t‖ *
          t ^ (s - 1).re
        ≤ M * t ^ (-1 : ℝ) * (C * t ^ (-a)) * t ^ (s - 1).re := by
          gcongr
      _ = M * C * (t ^ (-1 : ℝ) * t ^ (-a) * t ^ (s - 1).re) := by ring
  -- pointwise form of the integrand
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, Lf κ b t * g t * (t : ℂ) ^ (s - 1) =
      slantDir κ * ∫ u, F t u ∂ν := by
    intro t _
    rw [Lf, intervalIntegral.integral_of_le h1b, mul_assoc, mul_assoc]
    congr 1
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF]
    ring
  have hInner : Integrable (fun t => ∫ u, F t u ∂ν) μ := hInt.integral_prod_left
  refine ⟨?_, ?_⟩
  · exact (hInner.const_mul (slantDir κ)).congr
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => (hpt t ht).symm))
  · rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
      integral_integral_swap hInt, intervalIntegral.integral_of_le h1b]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hF]
    rw [← lf_cpow_mul ht.1 s]
    ring

theorem integral_Lf_cpow {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => Lf κ b t * (t : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, Lf κ b t * (t : ℂ) ^ (z - 1) = Yf κ b z := by
  have h := integral_Lf_mul (κ := κ) hb (g := fun _ => (1 : ℂ)) (a := 0) (C := 1)
    aestronglyMeasurable_const (fun t ht => by simp) (s := z) (by linarith)
  simp only [mul_one, one_mul] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Yf]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (by linarith [hb.2])] at hu
  rw [TIdentity.integral_Ioc_cpow_of_neg_one_lt]
  · have e : z - 1 + (u : ℂ) * slantDir κ - 1 + 1 = z - 1 + (u : ℂ) * slantDir κ := by ring
    rw [e, mul_one_div]
  · simp [slantDir]
    linarith [hu.1]

theorem lf_isCompact_Sseg (κ b : ℝ) : IsCompact (Sseg κ b) := by
  have : Sseg κ b = (fun u : ℝ => 1 - (u : ℂ) * slantDir κ) '' Icc 0 (1 - b) := by
    ext z
    simp only [Sseg, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [this]
  exact isCompact_Icc.image (by fun_prop)

theorem analyticOnNhd_Yf {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (Yf κ b) (Sseg κ b)ᶜ := by
  have hU : IsOpen (Sseg κ b)ᶜ := (lf_isCompact_Sseg κ b).isClosed.isOpen_compl
  have h1b : (0 : ℝ) ≤ 1 - b := by linarith [hb.2]
  have hne : ∀ z ∈ (Sseg κ b)ᶜ, ∀ u ∈ [[(0 : ℝ), 1 - b]], z - 1 + (u : ℂ) * slantDir κ ≠ 0 := by
    intro z hz u hu h
    rw [uIcc_of_le h1b] at hu
    exact hz ⟨u, hu, by linear_combination h⟩
  have hD : DifferentiableOn ℂ (fun z => ∫ u in (0 : ℝ)..(1 - b),
      Gamma (1 - (u : ℂ) * slantDir κ) / (z - 1 + (u : ℂ) * slantDir κ)) (Sseg κ b)ᶜ := by
    refine differentiableOn_intervalIntegral_of_continuousOn hU ?_ ?_
    · intro p hp
      refine ContinuousAt.continuousWithinAt ?_
      have hu := hp.2
      rw [uIcc_of_le h1b] at hu
      have hG : ContinuousAt (fun p : ℂ × ℝ => Gamma (1 - (p.2 : ℂ) * slantDir κ)) p :=
        (lf_continuousAt_Gamma (κ := κ) (by linarith [hu.2, hb.1])).comp
          continuous_snd.continuousAt
      exact hG.div (by fun_prop) (hne p.1 hp.1 p.2 hp.2)
    · intro u hu z hz
      have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1 + (u : ℂ) * slantDir κ) z := by fun_prop
      exact ((differentiableAt_const _).div h1 (hne z hz u hu)).differentiableWithinAt
  have : DifferentiableOn ℂ (Yf κ b) (Sseg κ b)ᶜ := by
    have h2 := hD.const_mul (slantDir κ)
    exact h2.congr fun z _ => rfl
  exact this.analyticOnNhd hU

end GroupE

end GoldbachBoundaries.ThmA
