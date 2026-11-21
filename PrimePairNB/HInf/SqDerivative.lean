import PrimePairNB.HInf.SqKernel
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.Jv_analyticOn

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

/-- Differentiate the finite collision sum at its centre. -/
theorem deriv_Xc_Sq (hZ1 : Z1) (hZ6 : Z6) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt ⊤) :
    deriv (Xc kSq x) x = pairSumSq x := by
  have := Fill.finite_pairs hZ1 hx
  have := Fintype.ofFinite (pinchPairs x)
  have he : Xc kSq x = fun v => ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv kSq p.1.1 p.1.2 v := by
    funext v
    exact tsum_fintype _
  have hterm : ∀ p : pinchPairs x, HasDerivAt
      (fun v => cP p.1.1 * cP p.1.2 * Jv kSq p.1.1 p.1.2 v)
      (Rcoef p.1.1 * Rcoef p.1.2 * kSq p.1.1 x) x := by
    intro p
    have hJ := Fill.hasDerivAt_Jv (isPinchKernel_Sq_top hZ6) p.2.1 p.2.2.1
      (by rw [p.2.2.2]; exact hxV)
    rw [p.2.2.2] at hJ
    simpa only [cP, neg_mul_neg] using hJ.const_mul (cP p.1.1 * cP p.1.2)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hterm p)
  rw [he, hs.deriv]
  exact (tsum_fintype _).symm

end GoldbachBoundaries.HInf
