import PrimePairNB.HInf.Fill.Jv_analyticOn

/-!
# `Xc_analyticOn`, `MSpanK_analyticOn`

On `Xcat`, `Xc k x` is a finite sum (`M1.pinchPairs_finite`), and every term is holomorphic on `𝒱` or vanishes at `x`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- The pairs of a catalogue point are a finite type. -/
lemma finite_pairs (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat) : Finite (pinchPairs x) :=
  (M1.pinchPairs_finite hZ1 hx.2).to_subtype

/-- `X_x` is holomorphic on all of `𝒱` (a finite sum, `Paper2.M1.pinchPairs_finite`). -/
theorem Xc_analyticOn (hZ1 : Z1) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D) {x : ℂ}
    (hx : x ∈ Xcat) : AnalyticOnNhd ℂ (Xc k x) (Vt top) := by
  have := finite_pairs hZ1 hx
  have := Fintype.ofFinite (pinchPairs x)
  have hd : DifferentiableOn ℂ (fun v => ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv k p.1.1 p.1.2 v) (Vt top) := by
    refine DifferentiableOn.fun_sum fun p _ => ?_
    exact ((Jv_analyticOn hK p.2.1 p.2.2.1).differentiableOn).const_mul _
  have he : Xc k x = fun v => ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv k p.1.1 p.1.2 v := by
    funext v
    exact tsum_fintype _
  rw [he]
  exact hd.analyticOnNhd (isOpen_Vt top)

/-- Every member of `𝓜` is holomorphic on all of `𝒱`. -/
theorem MSpanK_analyticOn (hZ1 : Z1) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D)
    {m : ℂ → ℂ} (hm : m ∈ MSpanK k) : AnalyticOnNhd ℂ m (Vt top) := by
  induction hm using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    exact fun v hv => analyticAt_const.mul (Xc_analyticOn hZ1 hK hx v hv)
  | zero => exact fun v _ => analyticAt_const
  | add f g _ _ hf hg => exact fun v hv => (hf v hv).add (hg v hv)
  | neg f _ hf => exact fun v hv => (hf v hv).neg

end GoldbachBoundaries.HInf.Fill

