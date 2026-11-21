import PrimePairNB.HInf.Fill.isPinchKernel_S

/-!
# `deriv_Jv_kS_extends`

In the variable `s = (v - 1)/2`, `J_{ab}` is `Paper2.Jseg Aff.twoOneL kerS a b`, and (H2b) for `kerS` gives its derivative
(`M4a.hasDerivAt_Jseg_of_H2b`). The chain rule's factor `½` gives `J'_{ab}(v) = ¼ [K((v - 2b + 3)/4) + K((2a - v + 3)/4)]`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `J_{ab}` for `kS` is `Jseg` for `kerS`. -/
lemma Jv_kS_eq_Jseg (a b v : ℂ) : Jv kS a b v = Jseg Aff.twoOneL kerS a b ((v - 1) / 2) := by
  simp only [Jv, Jseg, kS, app_twoOneL_half]

/-- The formula for `J'_{ab}` on `𝒱`. -/
theorem hasDerivAt_Jv_kS {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) {v : ℂ} (hv : v ∈ Vt 3) :
    HasDerivAt (Jv kS a b) ((1 / 4) * (KS ((v - 2 * b + 3) / 4) + KS ((2 * a - v + 3) / 4))) v := by
  have hv3 : v.re < 3 := re_lt_three_of_mem hv
  have hs : (v - 1) / 2 ∈ Aff.twoOneL.DL := by
    show 1 < (Aff.twoOneL.app ((v - 1) / 2)).re ∧ (Aff.twoOneL.app ((v - 1) / 2)).re < 3
    rw [app_twoOneL_half]
    exact ⟨hv.1, hv3⟩
  have hk : ∀ z s : ℂ, kerS z s = (fun w => (1 / 2) * KS ((w + 1) / 2)) (z - ((1 : ℝ) : ℂ) * s) := by
    intro z s
    simp only [kerS]
    congr 2
    push_cast
    ring
  have h := M4a.hasDerivAt_Jseg_of_H2b Aff.twoOneL kerS M4b.kerS_basic.1
    (g := fun w => (1 / 2) * KS ((w + 1) / 2)) (θ := 1) hk ha hb hs
  have hmap : HasDerivAt (fun v : ℂ => (v - 1) / 2) (1 / 2 : ℂ) v := by
    simpa using ((hasDerivAt_id v).sub_const (1 : ℂ)).div_const (2 : ℂ)
  have hc := h.comp v hmap
  have hfun : (Jv kS a b) = (Jseg Aff.twoOneL kerS a b) ∘ fun v : ℂ => (v - 1) / 2 := by
    funext v
    exact Jv_kS_eq_Jseg a b v
  rw [hfun]
  convert hc using 1
  rw [app_twoOneL_half]
  have e1 : (v - b - ((1 : ℝ) : ℂ) * ((v - 1) / 2) + 1) / 2 = (v - 2 * b + 3) / 4 := by
    push_cast
    ring
  have e2 : (a - ((1 : ℝ) : ℂ) * ((v - 1) / 2) + 1) / 2 = (2 * a - v + 3) / 4 := by
    push_cast
    ring
  simp only [e1, e2]
  have hell : ((Aff.twoOneL.ell : ℝ) : ℂ) = 2 := by simp [Aff.twoOneL]
  rw [hell]
  push_cast
  ring

/-- `K ∘ f` is meromorphic where `f` is analytic. -/
lemma meromorphicAt_KS_comp {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) : MeromorphicAt (fun x => KS (f x)) w :=
  (M4b.FillD.meromorphicAt_Gamma_comp hf).mul
    (M4b.FillD.meromorphicAt_Gamma_comp (f := fun x => 2 - f x) (analyticAt_const.sub hf))

/-- For `S`: `J'_{ab}` extends from `𝒱` to a function meromorphic on `ℂ`: in `s`,
`J'_{ab}(s) = ½K((s + 2 - b)/2) + ½K((a - s + 1)/2)`. From `Paper2.M4b.kerS_basic`. -/
theorem deriv_Jv_kS_extends {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) :
    ∃ g : ℂ → ℂ, MeromorphicOn g univ ∧ EqOn g (deriv (Jv kS a b)) (Vt 3) := by
  refine ⟨fun v => (1 / 4) * (KS ((v - 2 * b + 3) / 4) + KS ((2 * a - v + 3) / 4)), ?_, ?_⟩
  · intro v _
    exact (MeromorphicAt.const _ v).mul
      ((meromorphicAt_KS_comp (by fun_prop)).add (meromorphicAt_KS_comp (by fun_prop)))
  · intro v hv
    exact (hasDerivAt_Jv_kS ha hb hv).deriv.symm

end GoldbachBoundaries.HInf.Fill

