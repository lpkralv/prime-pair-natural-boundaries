import PrimePairNB.HInf.MixCoefficient
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

def sumMcMix (A : Set ℂ) (v : ℂ) : ℂ := ∑ᶠ x ∈ A ∩ Xcat, McMix x v

lemma MSpanK_analyticOn (hZ1 : Z1) (_hK : IsPinchKernel kerG ⊤ G)
    {m : ℂ → ℂ} (hm : m ∈ MSpanMix) : AnalyticOnNhd ℂ m (Vt ⊤) :=
  fun s hs => MSpanMix_analyticOn hZ1 hm s hs.1

/-- A finite sum of `M_x` over catalogue points lies in `𝓜`. -/
theorem sumMc_mem {A : Set ℂ} (hA : (A ∩ Xcat).Finite) : sumMcMix A ∈ MSpanMix := by
  classical
  have heq : sumMcMix A = ∑ x ∈ hA.toFinset, McMix x := by
    funext v
    simp only [sumMcMix, Finset.sum_apply]
    exact finsum_mem_eq_finite_toFinset_sum _ hA
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x hx => ?_
  exact AddSubgroup.subset_closure ⟨x, (hA.mem_toFinset.mp hx).2, rfl⟩

end GoldbachBoundaries.HInf.MixProof
