import PrimePairNB.HInf.Rotation
import PrimePairNB.HInf.Fill.admS_transfer
import PrimePairNB.HInf.Fill.continuesAlong_G
import PrimePairNB.HInf.Fill.deriv_Jv_kS_extends
import PrimePairNB.HInf.Fill.germFam_of_admissible_G
import PrimePairNB.HInf.Fill.germFam_of_admissible_S
import PrimePairNB.HInf.Fill.germFam_slope
import PrimePairNB.HInf.Fill.local_form_germFam
import PrimePairNB.HInf.Fill.uniformFamily_germFam

/-!
# HInf: every branch

Reuse: `ThmA.UniformFamily`, `ThmA.exists_continuationAlong_of_uniform`, `ThmA.continuationAlong_preserve`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Theorem 7.4.** `𝔊` is a uniform germ family on `𝒱_∞ ∖ X`, in the sense of `ThmA.UniformFamily`. -/
theorem uniformFamily_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (C : ℂ) : ThmA.UniformFamily (GermFam k top C) (VInf top \ Pinch) :=
  @Fill.uniformFamily_germFam hZ1 hZ2 hZ3 k top D hK C

/-- **Paper, Theorem 7.4.** `G` continues along every path in `{σ > 2B_∞} ∖ X` from `σ > 2`. Unconditional up to the premises. -/
theorem continuesAlong_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {γ : C(unitInterval, ℂ)}
    (hγ : ∀ t, γ t ∈ VInf ⊤ \ Pinch) (h0 : 2 < (γ 0).re) : ContinuesAlong G γ :=
  @Fill.continuesAlong_G hZ1 hZ2 hZ3 hZ6 γ hγ h0

/-- **Paper, Theorem 7.4.** Every germ reached from `σ > 2` along a path in `{σ > 2B_∞} ∖ X` is
`D^θ + m`. -/
theorem germFam_of_admissible_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn G (VInf ⊤ \ Pinch) (halfPlane 2) g q) : GermFam kerG ⊤ 0 q g :=
  @Fill.germFam_of_admissible_G hZ1 hZ2 hZ3 hZ6 g q hg

/-- **Paper, Theorem 7.4.** Near `x ∈ X`, every member of `𝔊` is `Log_θ(v - x) X_x + holomorphic`, with the same
`X_x` on every branch. `r` depends on `κ` and `x`, not on the germ. -/
theorem local_form_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf top ∧ ball x r \ rayW κ x ⊆ Om κ top ∧
      ∀ q ∈ ball x r \ rayW κ x, ∀ (C : ℂ) (f : ℂ → ℂ), GermFam k top C q f →
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball x r) ∧
          f =ᶠ[𝓝 q] fun v => logK κ (v - x) * Xc k x v + h v :=
  @Fill.local_form_germFam hZ1 hZ2 hZ3 k top D hK κ hκ x hx hxV

/-- For `S`: `J'_{ab}` extends from `𝒱` to a function meromorphic on `ℂ`: in `s`,
`J'_{ab}(s) = ½K((s + 2 - b)/2) + ½K((a - s + 1)/2)`. From `Paper2.M4b.kerS_basic`. -/
theorem deriv_Jv_kS_extends {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) :
    ∃ g : ℂ → ℂ, MeromorphicOn g univ ∧ EqOn g (deriv (Jv kS a b)) (Vt 3) :=
  @Fill.deriv_Jv_kS_extends a b ha hb

/-- **Paper, Theorem 7.4.** A germ reached from `Re v > 3` along a path in
`{Re v > 2B_∞} ∖ X` along which `S` continues, ending at `Re v < 3`, is `D^θ + m + C`. -/
theorem germFam_of_admissible_S (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn DS (halfPlane (2 * Binf) \ Pinch) (halfPlane 3) g q) (hq : q.re < 3) :
    ∃ C : ℂ, GermFam kS 3 C q g :=
  @Fill.germFam_of_admissible_S hZ1 hZ2 hZ3 g q hg hq

/-- Under `(H_∞)`, the change of variable `v = 2s + 1` carries `AdmS` to the hypothesis of `germFam_of_admissible_S`. -/
theorem admS_transfer (hZ1 : Z1) (hH : Hinf) {g : ℂ → ℂ} {s₁ : ℂ} (hg : AdmS g s₁) :
    IsAdmissibleGermOn DS (halfPlane (2 * Binf) \ Pinch) (halfPlane 3) (fun v => g ((v - 1) / 2)) (2 * s₁ + 1) :=
  @Fill.admS_transfer hZ1 hH g s₁ hg

end GoldbachBoundaries.HInf
