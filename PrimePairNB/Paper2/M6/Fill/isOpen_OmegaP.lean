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

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- A compact subset of `{Re z > 0}` meets `Σ` in a finite set (`poleSetQ_locallyFinite`). -/
lemma finite_inter_poleSetQ_A {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ halfPlane 0) :
    (K ∩ PoleSetQ).Finite := by
  classical
  have hU : ∀ x ∈ K, ∃ U ∈ 𝓝 x, (U ∩ PoleSetQ).Finite := fun x hx =>
    M1.poleSetQ_locallyFinite x (hK0 hx)
  choose! U hUn hUf using hU
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U hUn
  have hfin : (⋃ x ∈ t, U x ∩ PoleSetQ).Finite :=
    t.finite_toSet.biUnion fun x hx => hUf x (htK x hx)
  refine hfin.subset ?_
  rintro z ⟨hzK, hzP⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcov hzK)
  exact mem_iUnion₂.mpr ⟨x, hx, hzx, hzP⟩

end GoldbachBoundaries.Paper2.M6
