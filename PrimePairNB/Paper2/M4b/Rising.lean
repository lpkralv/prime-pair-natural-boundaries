import PrimePairNB.Paper2.M4b.MB
import PrimePairNB.Paper2.M4b.Fill.rising_summable_eq
import PrimePairNB.Paper2.M4b.Fill.rising_differentiableOn

/-!
# (R) for the combinations `∑ c_{ij}(s) p^i q^j (p+q)^{-s-i-j}` (`L(s) = s`)

The examples use one computation: the kernel of
`p^i q^j (p+q)^{-s-i-j}` is `Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`. In the form of `MB.lean`: `p^i q^j (p+q)^{-s-i-j} =
q^{-s} f(p/q)` with `f(t) = t^i(1+t)^{-(s+i+j)}`, whose kernel is `kMB 1 i (s+i+j) z = K_{s+i+j}(z+i)`. Summing over
`i, j < N` with coefficients `c_{ij}(s)` gives (R) (all but reality) for `Wrise N cf` and `krise N cf`, with `P`
(`ω = 1`) or `Q` (`ω = log`). The weights `W_G = (p+q)^{-s}` (`N = 1`, `c = 1`), `W₀` (`N = 2`) and `W_H`
(`cWH h`, definitionally) are instances; their kernels `K_s`, `k₀`, `k_H` equal `krise` on the lines used.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `rising_summable_eq`, `rising_differentiableOn`. -/

/-! ## Real lemmas -/

lemma WG_eq_Wrise (s : ℂ) (p q : ℕ) : WG s p q = Wrise 1 (fun _ _ _ => 1) s p q := by
  simp [WG, Wrise]

lemma kerG_eq_krise (z s : ℂ) : kerG z s = krise 1 (fun _ _ _ => 1) z s := by
  simp [kerG, krise, KerS]

lemma differentiableOn_one_cf (i j : ℕ) :
    DifferentiableOn ℂ ((fun _ _ _ => (1 : ℂ)) i j) (halfPlane 2) :=
  differentiableOn_const _

end GoldbachBoundaries.Paper2.M4b
