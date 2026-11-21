import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.Jv_analyticOn

/-!
# `deriv_Xc_G`

Differentiate the finite sum at `x`: each term gives `kerG a (a + b) = B(a, b)`, and `c(a) c(b) = R_a R_b`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- For `G`: `X_x'(x) = ∑ c(a) c(b) B(a,b) = pairSum x`. -/
theorem deriv_Xc_G (hZ1 : Z1) (hZ6 : Z6) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt ⊤) :
    deriv (Xc kerG x) x = pairSum x := by
  have := finite_pairs hZ1 hx
  have := Fintype.ofFinite (pinchPairs x)
  have hK := isPinchKernel_G hZ6
  have he : Xc kerG x = fun v => ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv kerG p.1.1 p.1.2 v := by
    funext v
    exact tsum_fintype _
  have key : ∀ a b : ℂ, a ∈ PoleSetQ → b ∈ PoleSetQ → a + b = x →
      HasDerivAt (fun v => cP a * cP b * Jv kerG a b v) (Rcoef a * Rcoef b * betaB a b) x := by
    intro a b ha hb hab
    have hJ := hasDerivAt_Jv hK ha hb (by rw [hab]; exact hxV)
    have hval : cP a * cP b * kerG a (a + b) = Rcoef a * Rcoef b * betaB a b := by
      simp [cP, kerG, KerS, betaB]
    rw [← hval]
    rw [hab] at hJ ⊢
    exact hJ.const_mul _
  have hterm : ∀ p : pinchPairs x, HasDerivAt (fun v => cP p.1.1 * cP p.1.2 * Jv kerG p.1.1 p.1.2 v)
      (Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2) x :=
    fun p => key _ _ p.2.1 p.2.2.1 p.2.2.2
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hterm p)
  rw [he, hs.deriv]
  exact (tsum_fintype _).symm

end GoldbachBoundaries.HInf.Fill

