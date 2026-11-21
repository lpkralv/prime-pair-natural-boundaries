import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Residue of `Q` at every point of `Σ_Q` is `R_a`** (no RH). With `S` the finite set of
`n` for which `n a` is `1` or a zero (`n Re a ≤ 1`), `analyticAt_Qcont_sub_sum` reduces to the finitely many
terms `μ(n) A(n z)`, each with residue `-μ(n) ord_{na} ζ / n` at `a` (`hasResidue_negLogDerivZeta_*`,
`HasResidue.comp_natCast_mul`); then reindex the finite sum as the `tsum` defining `Rcoef`. -/
theorem hasResidue_Qcont_Rcoef {a : ℂ} (ha : a ∈ PoleSetQ) : HasResidue Qcont a (Rcoef a) := by
  exact A_hasResidue_Qcont (re_pos_of_mem_poleSetQ ha)

end GoldbachBoundaries.Paper2.M1
