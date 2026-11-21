import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.Bsup_facts
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Every point of `Σ_Q` other than `1` has real part at most `B` (Z1, through `Bsup_facts`).
Uses: `poleSetQ_re_bounds`, `Bsup_facts`. -/
theorem poleSetQ_re_le_Bsup (hZ1 : Z1) {a : ℂ} (ha : a ∈ PoleSetQ) (ha1 : a ≠ 1) : a.re ≤ Bsup := by
  by_cases hz : a ∈ NontrivialZeros
  · exact (Bsup_facts hZ1).1 a hz
  · exact ((poleSetQ_re_bounds ha).2.2 ha1 hz).trans (Bsup_facts hZ1).2.1

end GoldbachBoundaries.Paper2.M1
