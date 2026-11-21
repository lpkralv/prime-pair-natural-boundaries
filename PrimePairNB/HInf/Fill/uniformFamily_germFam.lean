import PrimePairNB.HInf.Fill.germFam_slope
import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.pinch_countable

/-!
# `uniformFamily_germFam`

A point `p` of `𝒱_∞ ∖ X` lies in `Ω_κ₀` for some `κ₀` (all but countably many), and a ball about `p` stays there. By
`germFam_slope` every germ in the family on that ball is `D^κ₀ + m + C`, which is holomorphic on the whole ball.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **The step.** `𝔊` is a uniform germ family on `𝒱_∞ ∖ X`, in the sense of `ThmA.UniformFamily`. -/
theorem uniformFamily_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (C : ℂ) : ThmA.UniformFamily (GermFam k top C) (VInf top \ Pinch) := by
  intro p hp
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ, p ∈ Om κ₀ top := by
    obtain ⟨κ₀, hκ₀⟩ := ((countable_not_mem_Om hp.1 hp.2).dense_compl ℝ).nonempty
    exact ⟨κ₀, by simpa using hκ₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_Om hZ1 κ₀ top) p hκ₀
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  obtain ⟨m, hm, hfm⟩ := germFam_slope hZ1 hZ2 hZ3 hK hf (hball hq)
  have hA : AnalyticOnNhd ℂ (fun v => Dth k κ₀ v + m v + C) (ball p r) := fun z hz =>
    ((Dth_analyticOn hZ1 hZ2 hZ3 hK κ₀ z (hball hz)).add
      (MSpanK_analyticOn hZ1 hK hm z (hball hz).1.1)).add analyticAt_const
  exact ⟨_, hA, hfm.symm, fun q' hq' => ⟨κ₀, hball hq', m, hm, EventuallyEq.rfl⟩⟩

end GoldbachBoundaries.HInf.Fill
