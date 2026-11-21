import PrimePairNB.HInf.Fill.isPinchKernel_S
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.Jv_analyticOn

/-!
# `deriv_Xc_S`

Differentiate the finite sum at `x`: each term gives `kS a (a + b) = ½ K((a - b + 3)/4)`, and `c(a) c(b) = R_a R_b`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- For `S`, in the variable `v`: `X_x'(x) = ½ ∑ c(a) c(b) K((a - b + 3)/4)`; in `s` the factor `½` disappears. -/
theorem deriv_Xc_S (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt 3) :
    deriv (Xc kS x) x = (1 / 2) * pairSumS x := by
  have := finite_pairs hZ1 hx
  have := Fintype.ofFinite (pinchPairs x)
  have hK := isPinchKernel_S
  have he : Xc kS x = fun v => ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv kS p.1.1 p.1.2 v := by
    funext v
    exact tsum_fintype _
  have key : ∀ a b : ℂ, a ∈ PoleSetQ → b ∈ PoleSetQ → a + b = x →
      HasDerivAt (fun v => cP a * cP b * Jv kS a b v)
        ((1 / 2) * (Rcoef a * Rcoef b * KS ((a - b + 3) / 4))) x := by
    intro a b ha hb hab
    have hJ := hasDerivAt_Jv hK ha hb (by rw [hab]; exact hxV)
    have hval : cP a * cP b * kS a (a + b) = (1 / 2) * (Rcoef a * Rcoef b * KS ((a - b + 3) / 4)) := by
      have harg : (a - (a + b - 1) / 2 + 1) / 2 = (a - b + 3) / 4 := by ring
      simp only [cP, kS, kerS, harg]
      ring
    rw [← hval]
    rw [hab] at hJ ⊢
    exact hJ.const_mul _
  have hterm : ∀ p : pinchPairs x, HasDerivAt (fun v => cP p.1.1 * cP p.1.2 * Jv kS p.1.1 p.1.2 v)
      ((1 / 2) * (Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4))) x :=
    fun p => key _ _ p.2.1 p.2.2.1 p.2.2.2
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hterm p)
  rw [he, hs.deriv, ← Finset.mul_sum]
  congr 1
  exact (tsum_fintype _).symm

end GoldbachBoundaries.HInf.Fill

