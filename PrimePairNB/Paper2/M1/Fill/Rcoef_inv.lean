import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `R_{1/k} = μ(k)/k` for `k ≥ 2` squarefree: `j/k` is real, never a zero (`riemannZeta_ne_zero_of_mem_Ioo`,
`riemannZeta_ne_zero_of_one_le_re`), and is `1` only for `j = k`. -/
theorem Rcoef_inv {k : ℕ} (hk : 2 ≤ k) (hsq : Squarefree k) : Rcoef (1 / (k : ℂ)) = mu k / k := by
  exact (A_hasResidue_Qcont (one_div_natCast_re_pos (by omega : k ≠ 0))).unique
    (hasResidue_Qcont_inv hk)

end GoldbachBoundaries.Paper2.M1
