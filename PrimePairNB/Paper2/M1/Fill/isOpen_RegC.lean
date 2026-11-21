import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The region `RegC δ c` is open (`F_δ` is finite, Z1). Uses: `Fdelta_spec`. -/
theorem isOpen_RegC (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) : IsOpen (RegC δ c) := by
  have hF := (Fdelta_spec hZ1 δ h.1).1
  have heq : RegC δ c = halfPlane (c + Binf + 2 * δ) ∩
      ⋂ a ∈ Fdelta δ, {s : ℂ | s.re ≠ c + a.re} := by
    ext s
    simp [RegC, halfPlane]
  rw [heq]
  exact (isOpen_halfPlane _).inter (hF.isOpen_biInter fun a _ =>
    isOpen_ne.preimage Complex.continuous_re)

end GoldbachBoundaries.Paper2.M1
