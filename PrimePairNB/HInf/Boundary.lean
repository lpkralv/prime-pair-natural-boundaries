import PrimePairNB.HInf.Branches
import PrimePairNB.HInf.Arith
import PrimePairNB.HInf.Fill.boundary_G
import PrimePairNB.HInf.Fill.boundary_S
import PrimePairNB.HInf.Fill.cor_domain_G
import PrimePairNB.HInf.Fill.cor_domain_S
import PrimePairNB.HInf.Fill.every_path_G
import PrimePairNB.HInf.Fill.every_path_S
import PrimePairNB.HInf.Fill.every_path_stays_G
import PrimePairNB.HInf.Fill.every_path_stays_S
import PrimePairNB.HInf.Fill.no_extension_any_path_G
import PrimePairNB.HInf.Fill.no_extension_any_path_S
import PrimePairNB.HInf.Fill.not_analytic_of_germFam

/-!
# HInf: the natural boundary

The natural boundary of `G` and `S` under `(H_∞)`, in the forms: no extension to a disc, the domain version, and
the any-path versions.

Reuse: `ThmA.no_analytic_across_log` (in `v`, where `Re x > 1`), `ThmA.exists_path_into`,
`ThmA.exists_meromorphic_update`, `ThmA.isTerminalGerm_trans_proof`, `ThmA.exists_component_reaching_line`,
`ThmA.exists_firstExit`, `ThmA.isTerminalGerm_restrict`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **The contradiction behind the boundary theorem, in `v`.** `X_x'(x) ≠ 0`, `F` analytic on the punctured disc, and the germ of `F` at one
point of the slit disc lies in `𝔊`: impossible. -/
theorem not_analytic_of_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top)
    (hX : deriv (Xc k x) x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball x r \ rayW κ x ⊆ Om κ top ∧ ∀ r' : ℝ, 0 < r' → r' ≤ r → ∀ F : ℂ → ℂ,
      (∀ s ∈ ball x r', s ≠ x → AnalyticAt ℂ F s) → ∀ q ∈ ball x r' \ rayW κ x, ∀ C : ℂ,
        ¬ GermFam k top C q F :=
  @Fill.not_analytic_of_germFam hZ1 hZ2 hZ3 k top D hK κ hκ x hx hxV hX

/-- **Paper, Theorem 1.2.** -/
theorem boundary_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmG g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) :=
  @Fill.boundary_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 g s₁ hg y r hr hs₁

/-- **Paper, Theorem 1.2.** No (Z6). -/
theorem boundary_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmS g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball ((y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball ((y : ℂ) * I) r) :=
  @Fill.boundary_S hH hZ1 hZ2 hZ3 hZ4 hZ5 g s₁ hg y r hr hs₁

/-- **Paper, Theorem 8.2.** For `G`: no meromorphic extension over a connected open set that meets the line. -/
theorem cor_domain_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {g : ℂ → ℂ}
    {s₁ : ℂ} (hg : AdmG g s₁) {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W) (hWL : (W ∩ lineOne).Nonempty)
    (hs₁ : s₁ ∈ W) : ¬ GermExtendsMeromorphically g s₁ W :=
  @Fill.cor_domain_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 g s₁ hg W hWo hWc hWL hs₁

/-- **Paper, Theorem 8.2.** -/
theorem cor_domain_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmS g s₁) {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W) (hWL : (W ∩ {s : ℂ | s.re = 0}).Nonempty)
    (hs₁ : s₁ ∈ W) : ¬ GermExtendsMeromorphically g s₁ W :=
  @Fill.cor_domain_S hH hZ1 hZ2 hZ3 hZ4 hZ5 g s₁ hg W hWo hWc hWL hs₁

/-- **Paper, Corollary 8.3.** A germ reached from `σ > 2` along any path in `ℂ`, ending off the catalogue,
is admissible. The path may pass through catalogue points on a holomorphic germ, so this differs from
`Statements.rem_every_path`, whose "the path stays in `ℍ ∖ 𝒞`" needs `X_α ≠ 0` at every catalogue point, known under RH
only. -/
theorem every_path_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm G γ g) (h1 : γ 1 ∉ catG) :
    AdmG g (γ 1) :=
  @Fill.every_path_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 γ h0 g hg h1

/-- **Paper, Corollary 8.3.** -/
theorem every_path_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm Sser γ g) (h1 : γ 1 ∉ catS) :
    AdmS g (γ 1) :=
  @Fill.every_path_S hH hZ1 hZ2 hZ3 hZ4 hZ5 γ h0 g hg h1

/-- **No extension along any path, `G`.** The terminal germ of `G` along
any path from `σ > 2`, ending at any point of the disc, does not extend meromorphically over the disc, even if the end point
is in `catG` (on a holomorphic germ). Proof: move the end point inside the disc of holomorphy to a point off `catG`;
`every_path_G` and `boundary_G` then apply to the nearby germ. -/
theorem no_extension_any_path_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm G γ g) (y r : ℝ) (hr : 0 < r)
    (h1 : γ 1 ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g (γ 1) (ball (1 + (y : ℂ) * I) r) :=
  @Fill.no_extension_any_path_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 γ h0 g hg y r hr h1

/-- **A continuation of `G` stays in `σ > 1`.** From `no_extension_any_path_G`, using `catG ⊆ HH`. -/
theorem every_path_stays_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) (hc : ContinuesAlong G γ) (t : unitInterval) : 1 < (γ t).re :=
  @Fill.every_path_stays_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 γ h0 hc t

/-- **No extension along any path, `S`.** As `no_extension_any_path_G`, from `σ > 1`, at the line `σ = 0`. -/
theorem no_extension_any_path_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm Sser γ g) (y r : ℝ) (hr : 0 < r)
    (h1 : γ 1 ∈ ball ((y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g (γ 1) (ball ((y : ℂ) * I) r) :=
  @Fill.no_extension_any_path_S hH hZ1 hZ2 hZ3 hZ4 hZ5 γ h0 g hg y r hr h1

/-- **A continuation of `S` stays in `σ > 0`.** -/
theorem every_path_stays_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) (hc : ContinuesAlong Sser γ) (t : unitInterval) : 0 < (γ t).re :=
  @Fill.every_path_stays_S hH hZ1 hZ2 hZ3 hZ4 hZ5 γ h0 hc t

end GoldbachBoundaries.HInf
