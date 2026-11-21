import PrimePairNB.ThmA.Fill.ECommonLf
import PrimePairNB.ThmA.Fill.ECommonF0
import PrimePairNB.ThmA.Fill.F0_split
import PrimePairNB.ThmA.Fill.Pv_spec

/-!
# `M0_identity`

`∫_0^1 h₀(t) t^{z-1} dt = Γ(z) P_v(z) - e_∞(z) - Y(z)` on `U = {Re z > b} ∖ 𝒮`. Both sides are
holomorphic on `U`, which is preconnected, and they agree on `Re z > 1`; identity theorem.

Uses as black boxes: `F0_split`, `Pv_spec`, `differentiableOn_intervalIntegral_of_continuousOn`
(through `analyticOnNhd_Yf`), and `GroupE.F0_continuousOn`, `GroupE.mellin_F0`,
`GroupE.differentiable_e0inf` (ECommonF0).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

/-! ### Geometry of `U = {Re z > b} ∖ 𝒮` (prefix `lf_`) -/

theorem lf_slantDir_ne_zero (κ : ℝ) : slantDir κ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [slantDir] at this

/-- The linear functional `ℓ'(z) = Im z - κ (Re z - 1)`; `𝒮 ⊆ {ℓ' = 0}`. -/
def lf_ell (κ : ℝ) (z : ℂ) : ℝ := z.im - κ * (z.re - 1)

theorem lf_ell_Sseg {κ b : ℝ} {z : ℂ} (hz : z ∈ Sseg κ b) : lf_ell κ z = 0 ∧ z.re ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := hz
  simp only [lf_ell, slantDir, sub_re, one_re, mul_re, ofReal_re, ofReal_im, add_re, mul_im,
    add_im, one_im, I_re, I_im, sub_im]
  constructor
  · ring
  · nlinarith [hu.1]

/-- A point of `{ℓ' = 0}` with `b < Re z ≤ 1` lies on `𝒮`. -/
theorem lf_mem_Sseg_of_ell {κ b : ℝ} {z : ℂ} (hℓ : lf_ell κ z = 0) (hb : b < z.re)
    (h1 : z.re ≤ 1) : z ∈ Sseg κ b := by
  refine ⟨1 - z.re, ⟨by linarith, by linarith⟩, ?_⟩
  simp only [lf_ell] at hℓ
  apply Complex.ext
  · simp [slantDir]
  · simp [slantDir]; linarith

theorem lf_mem_slitPlane {κ b : ℝ} {z : ℂ} (hz : b < z.re) (hzS : z ∉ Sseg κ b) :
    (z - 1) / slantDir κ ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  set w := (z - 1) / slantDir κ with hw
  have hzw : z = 1 + w * slantDir κ := by
    rw [hw]; field_simp [lf_slantDir_ne_zero κ]; ring
  have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  apply hzS
  refine ⟨-w.re, ⟨by linarith, ?_⟩, ?_⟩
  · have : z.re = 1 + w.re := by rw [hzw, hwr]; simp [slantDir]
    linarith
  · rw [hzw]; nth_rewrite 1 [hwr]; push_cast; ring

theorem lf_comb_pos {p q A B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hA : 0 < A)
    (hB : 0 < B) : 0 < p * A + q * B := by
  rcases hp.lt_or_eq with hp' | hp'
  · have := mul_pos hp' hA
    nlinarith [mul_nonneg hq hB.le]
  · subst hp'
    have hq1 : q = 1 := by linarith
    subst hq1
    simpa using hB

theorem lf_convex_pos (κ b : ℝ) : Convex ℝ {z : ℂ | b < z.re ∧ 0 < lf_ell κ z} := by
  intro x hx y hy p q hp hq hpq
  simp only [mem_ofPred_eq, lf_ell, add_re, add_im, smul_re, smul_im, smul_eq_mul] at hx hy ⊢
  constructor
  · have h := lf_comb_pos hp hq hpq (sub_pos.2 hx.1) (sub_pos.2 hy.1)
    linear_combination h - b * hpq
  · have h := lf_comb_pos hp hq hpq hx.2 hy.2
    linear_combination h + κ * hpq

theorem lf_convex_neg (κ b : ℝ) : Convex ℝ {z : ℂ | b < z.re ∧ lf_ell κ z < 0} := by
  intro x hx y hy p q hp hq hpq
  simp only [mem_ofPred_eq, lf_ell, add_re, add_im, smul_re, smul_im, smul_eq_mul] at hx hy ⊢
  constructor
  · have h := lf_comb_pos hp hq hpq (sub_pos.2 hx.1) (sub_pos.2 hy.1)
    linear_combination h - b * hpq
  · have h := lf_comb_pos hp hq hpq (neg_pos.2 hx.2) (neg_pos.2 hy.2)
    linear_combination h - κ * hpq

theorem lf_U_eq {κ b : ℝ} (hb : b < 1) :
    {z : ℂ | b < z.re} \ Sseg κ b =
      ({z : ℂ | b < z.re ∧ 0 < lf_ell κ z} ∪ {z : ℂ | 1 < z.re}) ∪
        {z : ℂ | b < z.re ∧ lf_ell κ z < 0} := by
  ext z
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hz, hzS⟩
    rcases lt_trichotomy (lf_ell κ z) 0 with h | h | h
    · exact Or.inr ⟨hz, h⟩
    · refine Or.inl (Or.inr ?_)
      by_contra h1
      exact hzS (lf_mem_Sseg_of_ell h hz (not_lt.mp h1))
    · exact Or.inl (Or.inl ⟨hz, h⟩)
  · rintro ((⟨hz, h⟩ | h) | ⟨hz, h⟩)
    · exact ⟨hz, fun hS => by linarith [(lf_ell_Sseg hS).1]⟩
    · exact ⟨by linarith, fun hS => by linarith [(lf_ell_Sseg hS).2]⟩
    · exact ⟨hz, fun hS => by linarith [(lf_ell_Sseg hS).1]⟩

theorem lf_isPreconnected_U {κ b : ℝ} (hb : b < 1) :
    IsPreconnected ({z : ℂ | b < z.re} \ Sseg κ b) := by
  rw [lf_U_eq hb]
  have hp : (2 + ((κ + 1 : ℝ) : ℂ) * I) ∈ {z : ℂ | b < z.re ∧ 0 < lf_ell κ z} := by
    simp only [mem_ofPred_eq, lf_ell]; simp; constructor <;> linarith
  have hp' : (2 + ((κ + 1 : ℝ) : ℂ) * I) ∈ {z : ℂ | 1 < z.re} := by simp
  have hm : (2 + ((κ - 1 : ℝ) : ℂ) * I) ∈ {z : ℂ | b < z.re ∧ lf_ell κ z < 0} := by
    simp only [mem_ofPred_eq, lf_ell]; simp; constructor <;> linarith
  have hm' : (2 + ((κ - 1 : ℝ) : ℂ) * I) ∈
      {z : ℂ | b < z.re ∧ 0 < lf_ell κ z} ∪ {z : ℂ | 1 < z.re} := Or.inr (by simp)
  refine IsPreconnected.union _ hm' hm ?_ (lf_convex_neg κ b).isPreconnected
  exact IsPreconnected.union _ hp hp' (lf_convex_pos κ b).isPreconnected
    (convex_halfSpace_re_gt 1).isPreconnected

/-! ### The two sides -/

theorem lf_h0_aesm (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    AEStronglyMeasurable (h0 κ b) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  have hc : ContinuousOn (fun t : ℝ => (F0 t : ℂ) - Lf κ b t) (Ioc (0 : ℝ) 1) := by
    refine ContinuousOn.sub ?_ ((continuousOn_Lf hb0).mono Ioc_subset_Ioi_self)
    exact (continuous_ofReal.comp_continuousOn F0_continuousOn).mono Ioc_subset_Ioi_self
  refine (hc.aestronglyMeasurable measurableSet_Ioc).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
  show (F0 t : ℂ) - Lf κ b t = h0 κ b t
  rw [(F0_split hRH hb).1 t ht.1]
  ring

theorem lf_LHS_differentiableOn (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1))
      (halfPlane b) := by
  obtain ⟨C, hC⟩ := (F0_split hRH hb).2
  exact TIdentity.differentiableOn_integral_Ioc_cpow (lf_h0_aesm hRH hb)
    (fun t ht => hC t ht.1)

theorem lf_RHS_differentiableOn (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    DifferentiableOn ℂ (fun z : ℂ => Gamma z * Pv κ z - e0inf z - Yf κ b z)
      ({z : ℂ | b < z.re} \ Sseg κ b) := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  intro z hz
  have hre : b < z.re := hz.1
  refine DifferentiableAt.differentiableWithinAt ?_
  have hG : DifferentiableAt ℂ Gamma z := TIdentity.differentiableAt_Gamma_of_re_pos (by linarith [hb.1])
  have hP : DifferentiableAt ℂ (Pv κ) z :=
    ((Pv_spec hRH κ).2.1 z (by linarith [hb.1]) (lf_mem_slitPlane hre hz.2)).1.differentiableAt
  have hY : DifferentiableAt ℂ (Yf κ b) z := (analyticOnNhd_Yf hb0 z hz.2).differentiableAt
  exact ((hG.mul hP).sub (differentiable_e0inf z)).sub hY

/-- Agreement on `Re z > 1`. -/
theorem lf_eq_of_one_lt (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) {z : ℂ}
    (hz : 1 < z.re) :
    ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1) =
      Gamma z * Pv κ z - e0inf z - Yf κ b z := by
  have hb0 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  obtain ⟨hconv, hmel⟩ := mellin_F0 hz
  obtain ⟨hLint, hLeq⟩ := integral_Lf_cpow (κ := κ) hb0 hz
  have hFint : IntegrableOn (fun t : ℝ => (F0 t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) := by
    refine (hconv.mono_set Ioc_subset_Ioi_self).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [smul_eq_mul, mul_comm]
  have hsplit : ∫ t in Ioc (0 : ℝ) 1, (F0 t : ℂ) * (t : ℂ) ^ (z - 1) = Gamma z * P z - e0inf z := by
    rw [← hmel, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one))]
    have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) • (F0 t : ℂ) = e0inf z := by
      simp only [e0inf, smul_eq_mul, mul_comm]
    have hI : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) • (F0 t : ℂ) =
        ∫ t in Ioc (0 : ℝ) 1, (F0 t : ℂ) * (t : ℂ) ^ (z - 1) := by
      simp only [smul_eq_mul, mul_comm]
    rw [hE, hI]
    ring
  have hh : ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1) =
      ∫ t in Ioc (0 : ℝ) 1, ((F0 t : ℂ) * (t : ℂ) ^ (z - 1) - Lf κ b t * (t : ℂ) ^ (z - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(F0_split hRH hb).1 t ht.1]
    ring
  rw [hh, integral_sub hFint hLint, hsplit, hLeq, (Pv_spec hRH κ).1 z hz]

end GroupE

/-- **The Mellin identity for `h₀`** (proof of the decomposition: `M₀ = ΓP_v - e_∞ - Y` on
`{Re z > b} ∖ 𝒮`). Under RH.

Sketch. LHS is holomorphic on `Re z > b` (`differentiableOn_integral_Ioc_cpow`,
`TIdentity/G9g_HolomorphyIoc.lean`, with `F0_split`'s bound). For `Re z > 1`: `∫_0^1 F₀ t^{z-1} =
ΓP - e_∞` (`F0_mellin`, split at `1`), `∫_0^1 L t^{z-1} = Y(z)` (Fubini, `∫_0^1 t^{z-x-1} = 1/(z-x)`
for `Re(z-x) > 0`), so LHS `= ΓP - e_∞ - Y = ΓP_v - e_∞ - Y` (`Pv_spec`). RHS is holomorphic on the
connected open set `{Re z > b} ∖ 𝒮` (`Pv_spec`: off the ray there; `Y` off `𝒮`; `e_∞` entire, as
`e1`); identity theorem. -/
theorem M0_identity (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) {z : ℂ}
    (hz : b < z.re) (hzS : z ∉ Sseg κ b) :
    ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1) =
      Gamma z * Pv κ z - e0inf z - Yf κ b z := by
  set U : Set ℂ := {z : ℂ | b < z.re} \ Sseg κ b with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff
      (GroupE.lf_isCompact_Sseg κ b).isClosed
  have hL : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1)) U :=
    ((GroupE.lf_LHS_differentiableOn hRH hb).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)).mono sdiff_subset
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => Gamma z * Pv κ z - e0inf z - Yf κ b z) U :=
    (GroupE.lf_RHS_differentiableOn hRH hb).analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ U := by
    refine ⟨by simp; linarith [hb.2], fun hS => ?_⟩
    have := (GroupE.lf_ell_Sseg hS).2
    norm_num at this
  have hev : (fun z : ℂ => ∫ t in Ioc (0 : ℝ) 1, h0 κ b t * (t : ℂ) ^ (z - 1)) =ᶠ[𝓝 2]
      (fun z : ℂ => Gamma z * Pv κ z - e0inf z - Yf κ b z) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    exact GroupE.lf_eq_of_one_lt hRH hb hw
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR (GroupE.lf_isPreconnected_U hb.2) h2 hev
    ⟨hz, hzS⟩

end GoldbachBoundaries.ThmA
