import PrimePairNB.ThmA.G14_Geometry
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- `Ω_ℍ ∩ {σ > 2b}` is connected, for every `b < 1` and every slope.

Sketch. From `s ∈ Ω_ℍ ∩ R_b` the ray `s + [0,∞)v` stays in it: its real part increases, and a
point `s + t'v = α - tv` of `cut_α` would put `s = α - (t+t')v` on the line of `cut_α` below `α`
with `Re s > 1`, i.e. on `cut_α`. The ray reaches `{σ > 2}`, which is convex and inside
`Ω_ℍ ∩ R_b` (cut points have real part `≤ Re α ≤ 2`). So every point is joined to a fixed convex
set (`IsPreconnected.of_forall` / `isPreconnected_of_forall_pair` with the joined segments). -/
theorem isPreconnected_Omega_inter (κ : ℝ) {b : ℝ} (hb : b < 1) :
    IsPreconnected (Omega κ ∩ halfPlane (2 * b)) := by
  have hright : halfPlane 2 ⊆ Omega κ ∩ halfPlane (2 * b) := by
    intro s hs
    exact ⟨halfPlane_two_subset_Omega κ hs, by
      change 2 * b < s.re
      have : 2 < s.re := hs
      linarith⟩
  apply isPreconnected_of_forall (3 : ℂ)
  intro s hs
  let f : ℝ → ℂ := fun t => s + (t : ℂ) * slantDir κ
  have hf : Continuous f := by fun_prop
  have hstay : f '' Ici 0 ⊆ Omega κ ∩ halfPlane (2 * b) := by
    rintro w ⟨t, ht, rfl⟩
    change 0 ≤ t at ht
    have hre : (f t).re = s.re + t := by simp [f, slantDir]
    have hsH : 1 < s.re := hs.1.1
    have hsB : 2 * b < s.re := hs.2
    refine ⟨⟨by change 1 < (f t).re; rw [hre]; linarith, ?_⟩,
      by change 2 * b < (f t).re; rw [hre]; linarith⟩
    intro hcut
    obtain ⟨α, hα, u, hu, huα, he⟩ := mem_iUnion₂.mp hcut
    have hse : s = α - ((u + t : ℝ) : ℂ) * slantDir κ := by
      dsimp [f] at he
      push_cast
      linear_combination he
    have hu' : u + t < α.re - 1 := by
      have heR := congrArg Complex.re hse
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        slantDir, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul,
        add_zero, zero_add] at heR
      linarith
    exact hs.1.2 (mem_iUnion₂.mpr ⟨α, hα, u + t, by linarith, hu', hse⟩)
  have hray : IsPreconnected (f '' Ici 0) := isPreconnected_Ici.image f hf.continuousOn
  have hplane : IsPreconnected (halfPlane 2) := (convex_halfSpace_re_gt 2).isPreconnected
  let T : ℝ := max 0 (3 - s.re)
  have hT : 0 ≤ T := le_max_left _ _
  have hfar : f T ∈ halfPlane 2 := by
    change 2 < (f T).re
    simp only [f, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      slantDir, Complex.add_re, Complex.one_re, Complex.I_re, mul_zero, sub_zero,
      mul_one, zero_mul, add_zero]
    have := le_max_right 0 (3 - s.re)
    dsimp [T] at *
    linarith
  refine ⟨(f '' Ici 0) ∪ halfPlane 2, union_subset hstay hright,
    Or.inr (by change (2 : ℝ) < (3 : ℂ).re; norm_num), ?_,
    hray.union (f T) ⟨T, hT, rfl⟩ hfar hplane⟩
  left
  exact ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl), by simp [f]⟩

end GoldbachBoundaries.ThmA
