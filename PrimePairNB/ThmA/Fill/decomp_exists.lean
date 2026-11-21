import PrimePairNB.ThmA.Fill.ECommonF0
import PrimePairNB.ThmA.Fill.ECommonLf
import PrimePairNB.ThmA.Fill.F0_split
import PrimePairNB.ThmA.Fill.M0_identity
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

/-!
# `decomp_exists` (the decomposition)

`Γ(s)G(s) = 2N₁(s) - 𝒟(s) + H(s)` on `σ > 2` with `H = E_∞ - 2N₂ + R₀` holomorphic on `σ > 2b`:

* `E_∞(s) = ∫_1^∞ F₀² t^{s-1} dt` (entire, `differentiable_integral_Ioi_cpow`);
* `N₂(s) = v ∫_0^{1-b} Γ(1 - uv) e_∞(s - 1 + uv) du` (entire);
* `R₀(s) = ∫_0^1 h₀² t^{s-1} dt` (holomorphic on `σ > 2b`, `differentiableOn_integral_Ioc_cpow`).

The identity: split the Mellin integral of `F₀²` at `t = 1` (as `TIdentity.Gamma_mul_T_eq_split`),
expand `F₀ = L + h₀` on `(0, 1]` (`F0_split`), and evaluate `∫_0^1 L² t^{s-1} = 𝒟(s)`
(`integral_Lf_mul`, `integral_Lf_cpow`) and `∫_0^1 L h₀ t^{s-1} = N₁ - N₂ - 𝒟` (`integral_Lf_mul`,
`M0_identity`, `Pv_spec`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-- `E_∞(s) = ∫_1^∞ F₀(t)² t^{s-1} dt`. -/
def dec_Einf (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((F0 t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `N₂(s) = ∫_𝒮 Γ(x) e_∞(s - x) dx`. -/
def dec_N2 (κ b : ℝ) (s : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b),
    Gamma (1 - (u : ℂ) * slantDir κ) * e0inf (s - 1 + (u : ℂ) * slantDir κ)

/-- `R₀(s) = ∫_0^1 h₀(t)² t^{s-1} dt`. -/
def dec_R0 (κ b : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (h0 κ b t * h0 κ b t) * (t : ℂ) ^ (s - 1)

theorem dec_differentiable_Einf : Differentiable ℂ dec_Einf := by
  obtain ⟨C, hC⟩ := F0_le_exp
  refine TIdentity.differentiable_integral_Ioi_cpow (C := C ^ 2) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((F0_continuousOn.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht)).pow 2)).aestronglyMeasurable
      measurableSet_Ioi
  · have ht1 : 1 ≤ t := le_of_lt ht
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : F0 t ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (F0_nonneg t) (hC t ht1) 2
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (C * Real.exp (-t)) ^ 2 = C ^ 2 * Real.exp (-t) * Real.exp (-t) := by ring
    calc F0 t ^ 2 ≤ C ^ 2 * Real.exp (-t) * Real.exp (-t) := h3 ▸ h1
      _ ≤ C ^ 2 * Real.exp (-t) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = C ^ 2 * Real.exp (-t) := mul_one _

/-- `u ↦ Γ(1 - uv)` is continuous on `[0, 1-b]` (`Re(1 - uv) = 1 - u ≥ b > 0`). -/
theorem dec_continuousOn_Gamma_x {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ)) [[0, 1 - b]] := by
  intro u hu
  have hu' : u ≤ 1 - b := by
    rw [uIcc_of_le (by linarith [hb.2])] at hu
    exact hu.2
  have hre : 0 < (1 - (u : ℂ) * slantDir κ).re := by
    simp [slantDir]
    linarith [hb.1]
  have hc : Continuous (fun u : ℝ => 1 - (u : ℂ) * slantDir κ) := by fun_prop
  exact (ContinuousAt.comp (f := fun u : ℝ => 1 - (u : ℂ) * slantDir κ) (x := u)
    (TIdentity.differentiableAt_Gamma_of_re_pos hre).continuousAt hc.continuousAt).continuousWithinAt

/-- `Re(s - 1 + uv) = Re s - 1 + u`. -/
theorem dec_re_z (κ : ℝ) (s : ℂ) (u : ℝ) :
    (s - 1 + (u : ℂ) * slantDir κ).re = s.re - 1 + u := by
  simp [slantDir]

theorem dec_mem_uIcc {b u : ℝ} (hb : b < 1) (hu : u ∈ [[0, 1 - b]]) : 0 ≤ u ∧ u ≤ 1 - b := by
  rw [uIcc_of_le (by linarith)] at hu
  exact hu

theorem dec_differentiable_N2 {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    Differentiable ℂ (dec_N2 κ b) := by
  have hint : DifferentiableOn ℂ (fun s : ℂ => ∫ u in (0 : ℝ)..(1 - b),
      Gamma (1 - (u : ℂ) * slantDir κ) * e0inf (s - 1 + (u : ℂ) * slantDir κ)) univ := by
    refine differentiableOn_intervalIntegral_of_continuousOn isOpen_univ ?_ ?_
    · have hG := dec_continuousOn_Gamma_x (κ := κ) hb
      refine ContinuousOn.mul ?_ ?_
      · exact hG.comp continuous_snd.continuousOn fun p hp => hp.2
      · exact differentiable_e0inf.continuous.comp_continuousOn (by fun_prop)
    · intro u _
      exact (differentiable_e0inf.comp (by fun_prop)).const_mul _ |>.differentiableOn
  intro s
  exact ((hint s (mem_univ _)).differentiableAt univ_mem).const_mul _

theorem dec_differentiableOn_R0 (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    DifferentiableOn ℂ (dec_R0 κ b) (halfPlane (2 * b)) := by
  obtain ⟨hsplit, C, hC⟩ := F0_split hRH (κ := κ) hb
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  have hcont : ContinuousOn (h0 κ b) (Ioc (0 : ℝ) 1) := by
    refine ((Complex.continuous_ofReal.comp_continuousOn
      (F0_continuousOn.mono Ioc_subset_Ioi_self)).sub
        ((continuousOn_Lf (κ := κ) hb0).mono Ioc_subset_Ioi_self)).congr fun t ht => ?_
    simp only [Pi.sub_apply, Function.comp_apply, hsplit t ht.1]
    ring
  have hmeas : AEStronglyMeasurable (fun t : ℝ => h0 κ b t * h0 κ b t)
      (volume.restrict (Ioc 0 1)) := (hcont.mul hcont).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖h0 κ b t * h0 κ b t‖ ≤ C ^ 2 * t ^ (-(2 * b)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1 := hC t ht0
    have h0n : 0 ≤ C * t ^ (-b) := le_trans (norm_nonneg _) h1
    rw [norm_mul]
    calc ‖h0 κ b t‖ * ‖h0 κ b t‖ ≤ (C * t ^ (-b)) * (C * t ^ (-b)) :=
          mul_le_mul h1 h1 (norm_nonneg _) h0n
      _ = C ^ 2 * t ^ (-(2 * b)) := by
        rw [show -(2 * b) = -b + -b by ring, Real.rpow_add ht0]
        ring
  exact TIdentity.differentiableOn_integral_Ioc_cpow hmeas hbound

theorem dec_cwa {g : ℂ → ℂ} {f : ℝ → ℂ} {S : Set ℝ} {u : ℝ} (hg : ContinuousAt g (f u))
    (hf : Continuous f) : ContinuousWithinAt (fun x => g (f x)) S u :=
  (hg.comp hf.continuousAt).continuousWithinAt

end GroupE

open GroupE

/-- **the decomposition.** `Γ(s)G(s) = 2N₁(s) - 𝒟(s) + H̃_b(s)` on `σ > 2`, `H̃_b` holomorphic on
`σ > 2b`. Under RH.

Sketch. `ΓG = E_∞ + ∫_0^1 F₀² t^{s-1}` (`F0_mellin`, split at `1`; `E_∞` entire).
`F₀ = L + h₀` (`F0_split`): `∫_0^1 L² t^{s-1} = 𝒟(s)` (Fubini, `∫_0^1 t^{s-x-y-1} = 1/(s-x-y)`, then
the iterated form of `Dc`); `N(s) = ∫_0^1 L h₀ t^{s-1} = ∫_𝒮 Γ(x) M₀(s-x) dx` (Fubini, `σ > 1 + b`)
`= N₁ - N₂ - 𝒟` (`M0_identity` at `z = s - x`, `Re z > 1`, `Pv = P` there); `R₀ = ∫_0^1 h₀² t^{s-1}`
holomorphic on `σ > 2b` (`differentiableOn_integral_Ioc_cpow`). Take `H = E_∞ - 2N₂ + R₀`
(`N₂ = ∫_𝒮 Γ(x)e_∞(s-x)dx` entire). -/
theorem decomp_exists (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (halfPlane (2 * b)) ∧
      ∀ s : ℂ, 2 < s.re → Gamma s * G s = 2 * N1ser κ b s - Dc κ b s + H s := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  refine ⟨fun s => dec_Einf s - 2 * dec_N2 κ b s + dec_R0 κ b s, ?_, ?_⟩
  · exact ((dec_differentiable_Einf.differentiableOn.sub
      ((dec_differentiable_N2 hb0).differentiableOn.const_mul 2)).add
        (dec_differentiableOn_R0 hRH hb))
  intro s hs
  obtain ⟨hsplit, C, hC⟩ := F0_split hRH (κ := κ) hb
  obtain ⟨K, hK⟩ := norm_Lf_le (κ := κ) hb0
  -- measurability of `L` and `h₀` on `(0, 1]`
  have hLc : ContinuousOn (Lf κ b) (Ioc (0 : ℝ) 1) :=
    (continuousOn_Lf (κ := κ) hb0).mono Ioc_subset_Ioi_self
  have hhc : ContinuousOn (h0 κ b) (Ioc (0 : ℝ) 1) := by
    refine ((Complex.continuous_ofReal.comp_continuousOn
      (F0_continuousOn.mono Ioc_subset_Ioi_self)).sub hLc).congr fun t ht => ?_
    simp only [Pi.sub_apply, Function.comp_apply, hsplit t ht.1]
    ring
  have hLm := hLc.aestronglyMeasurable (μ := volume) measurableSet_Ioc
  have hhm := hhc.aestronglyMeasurable (μ := volume) measurableSet_Ioc
  -- `A = ∫ L·L·t^{s-1}`, `B = ∫ L·h₀·t^{s-1}`
  obtain ⟨hAi, hAe⟩ := integral_Lf_mul hb0 hLm (a := 1) hK (s := s) (by linarith)
  have hKb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖h0 κ b t‖ ≤ C * t ^ (-b) := fun t ht => hC t ht.1
  obtain ⟨hBi, hBe⟩ := integral_Lf_mul hb0 hhm (a := b) hKb (s := s) (by linarith [hb.2])
  obtain ⟨hconv, hmel⟩ := mellin_F0_sq hs
  -- pointwise expansion on `(0, 1]`
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((F0 t ^ 2 : ℝ) : ℂ)
      = Lf κ b t * Lf κ b t * (t : ℂ) ^ (s - 1) + 2 * (Lf κ b t * h0 κ b t * (t : ℂ) ^ (s - 1))
        + (h0 κ b t * h0 κ b t) * (t : ℂ) ^ (s - 1) := by
    intro t ht
    simp only [smul_eq_mul]
    push_cast
    rw [hsplit t ht.1]
    ring
  have hCi : IntegrableOn (fun t : ℝ => (h0 κ b t * h0 κ b t) * (t : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
    refine (((hconv.mono_set Ioc_subset_Ioi_self).sub hAi).sub (hBi.const_mul 2)).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply, hpt t ht]
    ring
  have hIoc : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((F0 t ^ 2 : ℝ) : ℂ)
      = (∫ t in Ioc (0 : ℝ) 1, Lf κ b t * Lf κ b t * (t : ℂ) ^ (s - 1))
        + 2 * (∫ t in Ioc (0 : ℝ) 1, Lf κ b t * h0 κ b t * (t : ℂ) ^ (s - 1))
        + dec_R0 κ b s := by
    have hB2 : IntegrableOn (fun t : ℝ => 2 * (Lf κ b t * h0 κ b t * (t : ℂ) ^ (s - 1)))
        (Ioc (0 : ℝ) 1) := hBi.const_mul 2
    have hAB : IntegrableOn (fun t : ℝ => Lf κ b t * Lf κ b t * (t : ℂ) ^ (s - 1)
        + 2 * (Lf κ b t * h0 κ b t * (t : ℂ) ^ (s - 1))) (Ioc (0 : ℝ) 1) := hAi.add hB2
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hAB hCi,
      integral_add hAi hB2, integral_const_mul]
    rfl
  have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • ((F0 t ^ 2 : ℝ) : ℂ) = dec_Einf s := by
    simp only [dec_Einf, smul_eq_mul, mul_comm]
  have hGG : Gamma s * G s = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((F0 t ^ 2 : ℝ) : ℂ))
      + dec_Einf s := by
    rw [← hmel, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one)), hE]
  -- facts along the segment
  have hzre : ∀ u ∈ [[(0 : ℝ), 1 - b]], 1 < (s - 1 + (u : ℂ) * slantDir κ).re := by
    intro u hu
    rw [dec_re_z]
    linarith [(dec_mem_uIcc hb.2 hu).1]
  have hzS : ∀ u ∈ [[(0 : ℝ), 1 - b]], s - 1 + (u : ℂ) * slantDir κ ∉ Sseg κ b := by
    intro u hu ⟨u', hu', heq⟩
    have h1 := congrArg Complex.re heq
    have h2 := hzre u hu
    rw [h1] at h2
    simp [slantDir] at h2
    linarith [hu'.1]
  have hzcont : Continuous fun u : ℝ => s - 1 + (u : ℂ) * slantDir κ := by fun_prop
  have hGx := dec_continuousOn_Gamma_x (κ := κ) hb0
  -- `∫ L·L·t^{s-1} = 𝒟(s)`
  have hA : ∫ t in Ioc (0 : ℝ) 1, Lf κ b t * Lf κ b t * (t : ℂ) ^ (s - 1) = Dc κ b s := by
    rw [hAe, Dc]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [(integral_Lf_cpow hb0 (hzre u hu)).2]
  -- `∫ L·h₀·t^{s-1} = N₁ - N₂ - 𝒟`
  have hB : ∫ t in Ioc (0 : ℝ) 1, Lf κ b t * h0 κ b t * (t : ℂ) ^ (s - 1)
      = N1ser κ b s - dec_N2 κ b s - Dc κ b s := by
    rw [hBe]
    have hcongr : EqOn (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ) *
        ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (s - 1 + (u : ℂ) * slantDir κ - 1))
        (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (s - 1 + (u : ℂ) * slantDir κ) *
            P (s - 1 + (u : ℂ) * slantDir κ) - Gamma (1 - (u : ℂ) * slantDir κ) * e0inf (s - 1 + (u : ℂ) * slantDir κ)
          - Gamma (1 - (u : ℂ) * slantDir κ) * Yf κ b (s - 1 + (u : ℂ) * slantDir κ)) [[(0 : ℝ), 1 - b]] := by
      intro u hu
      have h1 := hzre u hu
      simp only
      rw [M0_identity hRH hb (by linarith [hb.2]) (hzS u hu),
        (Pv_spec hRH κ).1 _ (show (s - 1 + (u : ℂ) * slantDir κ) ∈ HH from h1)]
      ring
    rw [intervalIntegral.integral_congr hcongr]
    -- interval integrability of the three pieces
    have hI1 : IntervalIntegrable (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ) *
        Gamma (s - 1 + (u : ℂ) * slantDir κ) * P (s - 1 + (u : ℂ) * slantDir κ)) volume 0 (1 - b) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (hGx.mul ?_).mul ?_
      · intro u hu
        have hre : 0 < (s - 1 + (u : ℂ) * slantDir κ).re := by linarith [hzre u hu]
        exact dec_cwa (f := fun u : ℝ => s - 1 + (u : ℂ) * slantDir κ)
          (TIdentity.differentiableAt_Gamma_of_re_pos hre).continuousAt hzcont
      · intro u hu
        have hmem : s - 1 + (u : ℂ) * slantDir κ ∈ halfPlane 1 := hzre u hu
        exact dec_cwa (f := fun u : ℝ => s - 1 + (u : ℂ) * slantDir κ)
          (P_differentiableOn.differentiableAt ((isOpen_halfPlane 1).mem_nhds hmem)).continuousAt
          hzcont
    have hI2 : IntervalIntegrable (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ) *
        e0inf (s - 1 + (u : ℂ) * slantDir κ)) volume 0 (1 - b) :=
      (hGx.mul (differentiable_e0inf.continuous.comp hzcont).continuousOn).intervalIntegrable
    have hI3 : IntervalIntegrable (fun u : ℝ => Gamma (1 - (u : ℂ) * slantDir κ) *
        Yf κ b (s - 1 + (u : ℂ) * slantDir κ)) volume 0 (1 - b) := by
      refine (hGx.mul ?_).intervalIntegrable
      intro u hu
      exact dec_cwa (f := fun u : ℝ => s - 1 + (u : ℂ) * slantDir κ)
        (analyticOnNhd_Yf hb0 _ (hzS u hu)).continuousAt hzcont
    rw [intervalIntegral.integral_sub (hI1.sub hI2) hI3, intervalIntegral.integral_sub hI1 hI2,
      N1ser, dec_N2, Dc]
    ring
  rw [hGG, hIoc, hA, hB]
  ring

/-! ### Lemmas that use `decomp_exists` -/

section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

/-- `H̃_b` has the properties `decomp_exists` asks for. -/
theorem Htil_spec (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    DifferentiableOn ℂ (Htil κ b) (halfPlane (2 * b)) ∧
      ∀ s : ℂ, 2 < s.re → Gamma s * G s = 2 * N1ser κ b s - Dc κ b s + Htil κ b s := by
  have h := decomp_exists hRH (κ := κ) hb
  have : Htil κ b = h.choose := by
    unfold Htil
    split_ifs with h'
    · rfl
    · exact absurd h h'
  rw [this]
  exact h.choose_spec

end

end GoldbachBoundaries.ThmA
