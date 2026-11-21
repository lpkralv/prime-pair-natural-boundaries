import PrimePairNB.HInf.Local
import PrimePairNB.HInf.Fill.germ_const
import PrimePairNB.HInf.Fill.jump_line
import PrimePairNB.HInf.Fill.rotation
import PrimePairNB.HInf.Fill.sumMc_mem

/-!
# HInf: rotation

How the sheet `D^κ` changes with the slope `κ`: constancy of the germ, the jump across one line,
and the change by a sum of `M_x` over the catalogue points in the swept sector.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Lemma 7.1.** If `v₁ ∈ Ω_κ` for every `κ` in an interval, the germ of `D^κ` at `v₁` is constant on it. -/
theorem germ_const (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {v₁ : ℂ} {κ₁ κ₂ : ℝ} (h : κ₁ ≤ κ₂) (hmem : ∀ κ ∈ Icc κ₁ κ₂, v₁ ∈ Om κ top) :
    Dth k κ₂ =ᶠ[𝓝 v₁] Dth k κ₁ :=
  @Fill.germ_const hZ1 hZ2 hZ3 k top D hK v₁ κ₁ κ₂ h hmem

/-- **Paper, Lemma 7.2.** `v₁ ∉ X`; the catalogue points on the open ray in direction `κ` are
finitely many; for slopes close enough on either side, `v₁ ∈ Ω_{κm}, Ω_{κp}` and `D^{κp} - D^{κm} = ∑ M_{x_i}`, as germs. -/
theorem jump_line (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {v₁ : ℂ} (hv₁ : v₁ ∈ VInf top) (hv₁X : v₁ ∉ Pinch) (κ : ℝ) :
    (rayE κ v₁ ∩ Xcat).Finite ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ κm ∈ Ioo (κ - δ) κ, ∀ κp ∈ Ioo κ (κ + δ),
      v₁ ∈ Om κm top ∧ v₁ ∈ Om κp top ∧
        Dth k κp =ᶠ[𝓝 v₁] fun v => Dth k κm v + sumMc k (rayE κ v₁) v :=
  @Fill.jump_line hZ1 hZ2 hZ3 k top D hK v₁ hv₁ hv₁X κ

/-- **Paper, Theorem 7.3.** If `v₁ ∈ Ω_κ ∩ Ω_κ'`, `κ < κ'`, then as germs at `v₁`, `D^{κ'} - D^κ = ∑ M_x` over
catalogue points in the open sector, a finite sum. -/
theorem rotation (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {v₁ : ℂ} {κ κ' : ℝ} (hκ : κ < κ') (h₁ : v₁ ∈ Om κ top) (h₂ : v₁ ∈ Om κ' top) :
    (sector v₁ κ κ' ∩ Xcat).Finite ∧
      Dth k κ' =ᶠ[𝓝 v₁] fun v => Dth k κ v + sumMc k (sector v₁ κ κ') v :=
  @Fill.rotation hZ1 hZ2 hZ3 k top D hK v₁ κ κ' hκ h₁ h₂

end GoldbachBoundaries.HInf
