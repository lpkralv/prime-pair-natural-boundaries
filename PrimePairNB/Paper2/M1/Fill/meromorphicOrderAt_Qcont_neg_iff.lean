import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- A point of `Σ_Q` is a pole of `Q` exactly when `R_a ≠ 0` (from `hasResidue_Qcont_Rcoef` and
`meromorphicOrderAt_Qcont_ge`: order `-1` gives a non-zero residue, order `≥ 0` gives residue `0`).
Uses: `hasResidue_Qcont_Rcoef`, `meromorphicOrderAt_Qcont_ge`. -/
theorem meromorphicOrderAt_Qcont_neg_iff {a : ℂ} (ha : a ∈ PoleSetQ) :
    meromorphicOrderAt Qcont a < 0 ↔ Rcoef a ≠ 0 := by
  have hm := meromorphicAt_Qcont (re_pos_of_mem_poleSetQ ha)
  have hr := A_hasResidue_Qcont (re_pos_of_mem_poleSetQ ha)
  constructor
  · intro ho hz
    have hsub : MeromorphicAt (fun z : ℂ => z - a) a := (analyticAt_id.sub analyticAt_const).meromorphicAt
    have hprod := hsub.mul hm
    have hpos : 0 < meromorphicOrderAt ((fun z : ℂ => z - a) * Qcont) a :=
      (tendsto_zero_iff_meromorphicOrderAt_pos hprod).1 (by simpa only [HasResidue, hz, Pi.mul_def] using hr)
    rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const] at hpos
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
    rw [← hn] at ho hpos
    have hnneg : n < 0 := by exact_mod_cast ho
    have hnpos : (0 : ℤ) < 1 + n := by exact_mod_cast hpos
    omega
  · intro hc
    rw [hr.meromorphicOrderAt_eq_neg_one hm hc]
    exact_mod_cast (by norm_num : (-1 : ℤ) < 0)

end GoldbachBoundaries.Paper2.M1
