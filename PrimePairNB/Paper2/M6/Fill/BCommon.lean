import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WG
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WT
import PrimePairNB.Paper2.M4b.Fill.E1Common
import PrimePairNB.Paper2.M4b.Fill.hypR_kerSq
import PrimePairNB.Paper2.M4b.Fill.hypR_kerS
import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'
import PrimePairNB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import PrimePairNB.Paper2.M1.Fill.BCommon

/-!
# Shared helpers

* `B_exists_primitive_ball`: a function holomorphic on a ball has a primitive there (Mathlib's
  `DifferentiableOn.isExactOn_ball`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- A function holomorphic on a ball has a primitive on it (Morera, `DifferentiableOn.isExactOn_ball`). -/
theorem B_exists_primitive_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball c r)) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball c r, HasDerivAt Φ (g z) z :=
  hg.isExactOn_ball

end GoldbachBoundaries.Paper2.M6
