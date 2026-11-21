import PrimePairNB.HInf.MixDefs
import PrimePairNB.HInf.Fill.Xc_analyticOn

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

theorem XcMix_analyticOn (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat) :
    AnalyticOnNhd ℂ (XcMix x) (halfPlane 1) := by
  classical
  letI : Finite (pinchPairs x) := (M1.pinchPairs_finite hZ1 hx.2).to_subtype
  letI := Fintype.ofFinite (pinchPairs x)
  have hg (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gamma z := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hi := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hi
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hd : DifferentiableOn ℂ
      (fun s => -∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 *
        (Gamma (s - p.1.2) * Gamma p.1.2 / Gamma s)) (halfPlane 1) := by
    apply DifferentiableOn.neg
    apply DifferentiableOn.fun_sum
    intro p _ s hs
    have hs1 : 1 < s.re := hs
    have hs0 : 0 < s.re := lt_trans (by norm_num) hs1
    have hb := (M1.poleSetQ_re_bounds p.2.2.1).2.1
    have hsb : 0 < (s - p.1.2).re := by
      simp only [sub_re]
      linarith
    exact (((((hg (s - p.1.2) hsb).comp s
      ((differentiableAt_id).sub_const p.1.2)).mul_const _).div (hg s hs0)
      (Complex.Gamma_ne_zero_of_re_pos hs0)).const_mul _).differentiableWithinAt
  have he : XcMix x = fun s => -∑ p : pinchPairs x,
      cP p.1.1 * cP p.1.2 * (Gamma (s - p.1.2) * Gamma p.1.2 / Gamma s) := by
    funext s
    simp only [XcMix, tsum_fintype, kerG, KerS, sub_sub_cancel]
  rw [he]
  exact hd.analyticOnNhd (isOpen_halfPlane 1)

theorem MSpanMix_analyticOn (hZ1 : Z1) {m : ℂ → ℂ} (hm : m ∈ MSpanMix) :
    AnalyticOnNhd ℂ m (halfPlane 1) := by
  induction hm using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    exact fun v hv => analyticAt_const.mul (XcMix_analyticOn hZ1 hx v hv)
  | zero => exact fun v _ => analyticAt_const
  | add f g _ _ hf hg => exact fun v hv => (hf v hv).add (hg v hv)
  | neg f _ hf => exact fun v hv => (hf v hv).neg

end GoldbachBoundaries.HInf
