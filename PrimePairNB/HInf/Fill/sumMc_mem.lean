import PrimePairNB.HInf.Defs

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- A finite sum of `M_x` over catalogue points lies in `𝓜`. -/
theorem sumMc_mem (k : ℂ → ℂ → ℂ) {A : Set ℂ} (hA : (A ∩ Xcat).Finite) : sumMc k A ∈ MSpanK k := by
  classical
  have heq : sumMc k A = ∑ x ∈ hA.toFinset, Mc k x := by
    funext v
    simp only [sumMc, Finset.sum_apply]
    exact finsum_mem_eq_finite_toFinset_sum _ hA
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x hx => ?_
  exact AddSubgroup.subset_closure ⟨x, (hA.mem_toFinset.mp hx).2, rfl⟩

end GoldbachBoundaries.HInf.Fill

