import PrimePairNB.Paper2.M4b.Rising

/-!
# Shared helpers for the example kernels

* `analyticAt_invGamma`, `analyticAt_invGamma_comp`, `meromorphicAt_Gamma_comp`: `1/Γ` is entire, so `Γ ∘ f` is
  meromorphic for analytic `f`.
* `differentiableAt_Gamma_of_re_pos`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace FillD

/-- `1/Γ` is analytic everywhere. -/
lemma analyticAt_invGamma (w : ℂ) : AnalyticAt ℂ (fun w => (Gamma w)⁻¹) w :=
  Complex.differentiable_one_div_Gamma.analyticAt w

/-- `1/Γ ∘ f` is analytic where `f` is. -/
lemma analyticAt_invGamma_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (fun q => (Gamma (f q))⁻¹) p :=
  (analyticAt_invGamma (f p)).comp hf

/-- `Γ ∘ f` is meromorphic where `f` is analytic. -/
lemma meromorphicAt_Gamma_comp {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    MeromorphicAt (fun x => Gamma (f x)) w := by
  have h := (analyticAt_invGamma_comp hf).meromorphicAt.inv
  convert h using 1
  funext x
  simp

/-- `Γ` is differentiable on `Re w > 0`. -/
lemma differentiableAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Gamma w :=
  differentiableAt_Gamma _ (fun m h => by
    rw [h] at hw; simp at hw; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])

end FillD

end GoldbachBoundaries.Paper2.M4b
