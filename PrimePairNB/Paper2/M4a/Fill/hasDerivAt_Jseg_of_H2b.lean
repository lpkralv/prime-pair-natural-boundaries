import PrimePairNB.Paper2.M4a.Defs
import PrimePairNB.SigmaFinite
import PrimePairNB.Density
import PrimePairNB.Paper2.M4a.Fill.segment_subset_Str
import PrimePairNB.Paper2.M4a.Fill.BCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- A primitive on a fixed translated strip identifies the integral for nearby parameters.
The segment FTC and primitive construction are from the RH development, `ThmA/Fill/CCommon.lean`. -/
/-- **The (H2b) derivative formula** ((K1), no RH). Fix `s₀ ∈ D_L`. (1) For `(z, s)` in the open (K1) domain,
`g` is `DifferentiableAt` at `z - θs`: `g w = k(w + θs, s)` near `w = z - θs` (fixed `s`), and `w ↦ (w + θs, s)` is
affine into the (K1) domain. (2) By `segment_subset_Str` the segment `[a, L(s) - b]` lies in `Str(s)` for `s` near
`s₀`, so `F(s, t) = g(a + tΔ(s) - θs)` is jointly continuous and `C¹` in `s` near `s₀`, `t ∈ [0, 1]`, with
`∂ₛF = (tℓ - θ) g'(φ)`. (3) Differentiate under the integral
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, or the RH development's
`ThmA.differentiableOn_intervalIntegral_of_continuousOn` and then identify the derivative) and apply the product rule
to `Δ(s) · ∫_0^1 F(s, t) dt`. (4) Fundamental theorem of calculus in `t`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) for `t ↦ t g(φ(t, s₀))` (derivative `g(φ) + tΔ g'(φ)`) and for
`t ↦ g(φ(t, s₀))` (derivative `Δ g'(φ)`), then `ring`. The RH development's `ThmA.GroupC.segFTC`, `ThmA.GroupC.hasDerivAt_segInt`
(file `ThmA/Fill/CCommon.lean`, import it) are segment-FTC lemmas of the same kind. -/
theorem hasDerivAt_Jseg_of_H2b (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {g : ℂ → ℂ} {θ : ℝ}
    (hk : ∀ z s, k z s = g (z - θ * s)) {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) {s : ℂ}
    (hs : s ∈ A.DL) :
    HasDerivAt (Jseg A k a b) (((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) s := by
  let V : Set ℂ := {w | w + θ * s ∈ A.Str s}
  have hVo : IsOpen V := by
    exact (isOpen_lt continuous_const (by fun_prop : Continuous fun w : ℂ => (w + θ * s).re)).inter
      (isOpen_lt (by fun_prop : Continuous fun w : ℂ => (w + θ * s).re) continuous_const)
  have hVc : Convex ℝ V := by
    intro x hx y hy u v hu hv huv
    change 0 < (u • x + v • y + θ * s).re ∧
      (u • x + v • y + θ * s).re < (A.app s).re
    change 0 < (x + θ * s).re ∧ (x + θ * s).re < (A.app s).re at hx
    change 0 < (y + θ * s).re ∧ (y + θ * s).re < (A.app s).re at hy
    simp only [add_re, smul_re, smul_eq_mul, mul_re, ofReal_re, ofReal_im,
      zero_mul, sub_zero] at *
    have e : u * (θ * s.re) + v * (θ * s.re) = θ * s.re := by
      calc
        _ = (u + v) * (θ * s.re) := by ring
        _ = θ * s.re := by rw [huv, one_mul]
    have eR : u * (A.app s).re + v * (A.app s).re = (A.app s).re := by
      calc
        _ = (u + v) * (A.app s).re := by ring
        _ = (A.app s).re := by rw [huv, one_mul]
    constructor
    · by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        simp [hv0, hu1]; exact hx.1
      · have hp := add_pos_of_nonneg_of_pos (mul_nonneg hu hx.1.le)
          (mul_pos (lt_of_le_of_ne hv (Ne.symm hv0)) hy.1)
        nlinarith
    · by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        simp [hv0, hu1]; exact hx.2
      · have hp := add_pos_of_nonneg_of_pos
          (mul_nonneg hu (sub_pos.mpr hx.2).le)
          (mul_pos (lt_of_le_of_ne hv (Ne.symm hv0)) (sub_pos.mpr hy.2))
        nlinarith [huv]
  have hg : DifferentiableOn ℂ g V := by
    intro w hw
    have hp : (w + θ * s, s) ∈ A.domK1 := ⟨hs, hw⟩
    have hd := (hK1.differentiableAt ((GroupB.isOpen_domain A (isOpen_DL A)).mem_nhds hp)).comp w
      (f := fun w : ℂ => (w + θ * s, s))
      (show DifferentiableAt ℂ (fun w : ℂ => (w + θ * s, s)) w by fun_prop)
    have he : (fun w => k (w + θ * s) s) = g := by
      funext w; rw [hk]; congr 1; ring
    change DifferentiableAt ℂ (fun w => k (w + θ * s) s) w at hd
    rw [he] at hd
    exact hd.differentiableWithinAt
  let lo : ℂ → ℂ := fun x => a - θ * x
  let hi : ℂ → ℂ := fun x => A.app x - b - θ * x
  have hlo : lo s ∈ V := by
    change a - θ * s + θ * s ∈ A.Str s
    simpa using (segment_subset_Str A ha hb hs.1 (left_mem_segment ℝ a (A.app s - b)))
  have hhi : hi s ∈ V := by
    change A.app s - b - θ * s + θ * s ∈ A.Str s
    simpa using (segment_subset_Str A ha hb hs.1 (right_mem_segment ℝ a (A.app s - b)))
  let F : ℂ → ℂ := fun z => ThmA.segInt g (lo s) z
  have hF : ∀ z ∈ V, HasDerivAt F (g z) z := fun z hz =>
    ThmA.GroupC.hasDerivAt_segInt hVo hVc hg hlo hz
  have hFd : DifferentiableOn ℂ F V := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hFeq : Jseg A k a b =ᶠ[𝓝 s] fun x => F (hi x) - F (lo x) := by
    have hnlo : ∀ᶠ x in 𝓝 s, lo x ∈ V :=
      (show Continuous lo by dsimp [lo]; fun_prop).continuousAt.eventually_mem (hVo.mem_nhds hlo)
    have hnhi : ∀ᶠ x in 𝓝 s, hi x ∈ V :=
      (show Continuous hi by dsimp [hi]; unfold Aff.app; fun_prop).continuousAt.eventually_mem (hVo.mem_nhds hhi)
    filter_upwards [hnlo, hnhi] with x hxlo hxhi
    have hFTC := ThmA.GroupC.segFTC hVo hVc hFd hxlo hxhi
    rw [hFTC]
    have he : hi x - lo x = A.app x - a - b := by dsimp [hi, lo]; ring
    rw [he]
    unfold Jseg
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have hw : lo x + (t : ℂ) * (A.app x - a - b) ∈ V := by
      rw [← he]
      exact ThmA.GroupC.seg_mem hVc hxlo hxhi (by simpa using ht)
    change k (a + (t : ℂ) * (A.app x - a - b)) x =
      deriv F (lo x + (t : ℂ) * (A.app x - a - b))
    rw [(hF _ hw).deriv, hk]
    congr 1
    dsimp [lo]; ring
  have hdhi : HasDerivAt hi ((A.ell : ℂ) - θ) s := by
    simpa [hi, Aff.app] using
      ((((hasDerivAt_id s).const_mul (A.ell : ℂ)).add_const (A.ell0 : ℂ)).sub_const b).fun_sub
        ((hasDerivAt_id s).const_mul (θ : ℂ))
  have hdlo : HasDerivAt lo (-(θ : ℂ)) s := by
    simpa [lo] using ((hasDerivAt_id s).const_mul (θ : ℂ)).const_sub a
  have hd := ((hF _ hhi).comp s hdhi).sub ((hF _ hlo).comp s hdlo)
  have hd' := hd.congr_of_eventuallyEq hFeq
  convert hd' using 1
  dsimp [hi, lo]
  ring

end GoldbachBoundaries.Paper2.M4a
