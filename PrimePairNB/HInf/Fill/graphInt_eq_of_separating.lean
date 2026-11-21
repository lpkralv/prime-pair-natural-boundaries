import PrimePairNB.HInf.Fill.norm_pairIntegrand_le
import PrimePairNB.HInf.Fill.graphInt_eq_of_homotopy
import PrimePairNB.HInf.Fill.hasDerivAt_Pth
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating
import PrimePairNB.HInf.Fill.isOpen_Uth

/-!
# `graphInt_eq_of_separating`, `Dth_eq_graphInt`

The homotopy of graphs runs in the open set where `z`, `v - z` are in `U_θ` and `Re z < Re v`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

theorem sheet_Pth_differentiableOn (κ : ℝ) : DifferentiableOn ℂ (Pth κ) (Uth κ) :=
  fun _ hz => (hasDerivAt_Pth hz).differentiableAt.differentiableWithinAt

/-- The integrand is holomorphic in `z`. -/
theorem sheet_pairIntegrand_differentiableOn {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) {v : ℂ} (hv : v ∈ Vt top) :
    DifferentiableOn ℂ (pairIntegrand k κ v)
      (Uth κ ∩ ((fun z => v - z) ⁻¹' Uth κ ∩ {z : ℂ | z.re < v.re})) := by
  unfold pairIntegrand
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · refine hK.holo.comp (f := fun z : ℂ => (z, v)) (by fun_prop) ?_
    rintro z ⟨hz, -, hzv⟩
    exact ⟨hv, hz.1, hzv⟩
  · exact (sheet_Pth_differentiableOn κ).mono inter_subset_left
  · refine (sheet_Pth_differentiableOn κ).comp (f := fun z : ℂ => v - z) (by fun_prop) ?_
    rintro z ⟨-, hz, -⟩
    exact hz

/-- The value does not depend on the separating graph. -/
theorem graphInt_eq_of_separating (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ₀ Γ₁ : SlantGraph κ}
    (h₀ : IsSeparating v Γ₀) (h₁ : IsSeparating v Γ₁) :
    graphInt Γ₀ (pairIntegrand k κ v) = graphInt Γ₁ (pairIntegrand k κ v) := by
  obtain ⟨ε₁, hε₁, hmem⟩ := interpPt_mem_of_separating h₀ h₁
  refine graphInt_eq_of_homotopy Γ₀ Γ₁
    (U := Uth κ ∩ ((fun z => v - z) ⁻¹' Uth κ ∩ {z : ℂ | z.re < v.re})) ?_
    (sheet_pairIntegrand_differentiableOn hK κ hv.1) ?_ (norm_pairIntegrand_le hZ1 hZ2 hZ3 hK hv h₀ h₁)
  · refine (isOpen_Uth κ).inter (((isOpen_Uth κ).preimage (by fun_prop)).inter ?_)
    exact isOpen_lt Complex.continuous_re continuous_const
  · intro l hl h
    obtain ⟨a, b, -, c⟩ := hmem l hl h
    exact ⟨a, b, by
      show (interpPt Γ₀ Γ₁ l h).re < v.re
      linarith⟩

/-- `D^θ(v)` is the integral over any separating graph. -/
theorem Dth_eq_graphInt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ : SlantGraph κ} (hΓ : IsSeparating v Γ) :
    Dth k κ v = graphInt Γ (pairIntegrand k κ v) := by
  have hex : ∃ Γ : SlantGraph κ, IsSeparating v Γ := ⟨Γ, hΓ⟩
  unfold Dth
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact graphInt_eq_of_separating hZ1 hZ2 hZ3 hK hv hex.choose_spec hΓ

end GoldbachBoundaries.HInf.Fill

