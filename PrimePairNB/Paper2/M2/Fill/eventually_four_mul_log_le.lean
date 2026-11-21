import PrimePairNB.Paper2.M2.Fill.BCommon

/-! `eventually_four_mul_log_le` (`Single.lean`). The proof is `eventually_four_mul_log_leB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `4X log(2X) = o(X²/log² X)`. (`isLittleO_log_rpow_atTop`, or `log X ≤ X^{1/4}` for large `X`.) -/
theorem eventually_four_mul_log_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X in atTop, 4 * X * Real.log (2 * X) ≤ c / 2 * X ^ 2 / Real.log X ^ 2 :=
  eventually_four_mul_log_leB hc

end GoldbachBoundaries.Paper2.M2
