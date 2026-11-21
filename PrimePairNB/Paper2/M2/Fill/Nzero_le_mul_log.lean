import PrimePairNB.Paper2.M2.Fill.BCommon

/-! `Nzero_le_mul_log` (`Single.lean`). The proof is `Nzero_le_mul_logB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`N(t) ≤ t log t` for large `t`** (Z2, first clause). `N(t) ≤ (t/2π) log(t/2π) - t/2π + C log t
≤ (t/2π) log t + C log t ≤ t log t` once `(1 - 1/2π) t ≥ |C|` and `t ≥ 2π` (so `log(t/2π) ≤ log t` and the middle
term is `≤ 0`). -/
theorem Nzero_le_mul_log (hZ2 : Z2) : ∀ᶠ t in atTop, Nzero t ≤ t * Real.log t :=
  Nzero_le_mul_logB hZ2

end GoldbachBoundaries.Paper2.M2
