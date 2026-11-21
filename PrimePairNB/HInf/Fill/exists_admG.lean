import PrimePairNB.HInf.Fill.boundary_G

/-!
# `exists_admG`
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `G` itself is an admissible germ at `3`. -/
theorem exists_admG : AdmG G 3 := admG_of_two_lt (by norm_num)

end GoldbachBoundaries.HInf.Fill
