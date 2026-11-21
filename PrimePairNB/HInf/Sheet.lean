import PrimePairNB.HInf.Kernels
import PrimePairNB.HInf.Separating
import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.Dth_eq
import PrimePairNB.HInf.Fill.graphInt_eq_of_separating
import PrimePairNB.HInf.Fill.norm_pairIntegrand_le

/-!
# HInf: the principal sheets `D^θ`

`D^θ(v)` is independent of the separating graph used, is holomorphic on `Ω_θ`, and equals `D` on `2 < Re v < 3`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Theorem 5.3.** The value does not depend on the separating graph. -/
theorem graphInt_eq_of_separating (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ₀ Γ₁ : SlantGraph κ}
    (h₀ : IsSeparating v Γ₀) (h₁ : IsSeparating v Γ₁) :
    graphInt Γ₀ (pairIntegrand k κ v) = graphInt Γ₁ (pairIntegrand k κ v) :=
  @Fill.graphInt_eq_of_separating hZ1 hZ2 hZ3 k top D hK κ v hv Γ₀ Γ₁ h₀ h₁

/-- `D^θ(v)` is the integral over any separating graph. -/
theorem Dth_eq_graphInt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ : SlantGraph κ} (hΓ : IsSeparating v Γ) :
    Dth k κ v = graphInt Γ (pairIntegrand k κ v) :=
  @Fill.Dth_eq_graphInt hZ1 hZ2 hZ3 k top D hK κ v hv Γ hΓ

/-- **Paper, Theorem 5.3.** `D^θ` is holomorphic on `Ω_θ`. -/
theorem Dth_analyticOn (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) : AnalyticOnNhd ℂ (Dth k κ) (Om κ top) :=
  @Fill.Dth_analyticOn hZ1 hZ2 hZ3 k top D hK κ

/-- **Paper, Theorem 5.3.** `D^θ = D` on `2 < Re v < 3`. -/
theorem Dth_eq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) (h3 : v.re < 3) : Dth k κ v = D v :=
  @Fill.Dth_eq hZ1 hZ2 hZ3 k top D hK κ v h2 h3

/-- `D^θ = G` on all of `σ > 2`, by the identity theorem from `Dth_eq` (`ThmA.G_differentiableOn`). -/
theorem Dth_eq_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) :
    Dth kerG κ v = G v :=
  @Fill.Dth_eq_G hZ1 hZ2 hZ3 hZ6 κ v h2

end GoldbachBoundaries.HInf
