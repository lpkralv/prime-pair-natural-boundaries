import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Q` has at most simple poles in `Re z > 0` (no RH): locally `Qcont` is finitely many terms `μ(n) A(n z)`,
each of order `≥ -1` (`A` has simple poles), plus an analytic function. -/
theorem meromorphicOrderAt_Qcont_ge {a : ℂ} (ha : 0 < a.re) : -1 ≤ meromorphicOrderAt Qcont a := by
  exact (A_hasResidue_Qcont ha).neg_one_le_meromorphicOrderAt (meromorphicAt_Qcont ha)

end GoldbachBoundaries.Paper2.M1
