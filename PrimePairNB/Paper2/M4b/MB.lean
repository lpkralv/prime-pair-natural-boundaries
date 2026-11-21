import PrimePairNB.Paper2.M4b.Defs
import PrimePairNB.Paper2.M4b.Fill.verticalIntegral'_comp_affine
import PrimePairNB.Paper2.M4b.Fill.mellinInv_kMB
import PrimePairNB.Paper2.M4b.Fill.tsum_eq_verticalIntegral'_of_mellin
import PrimePairNB.Paper2.M4b.Fill.differentiableOn_dser

/-!
# One Mellin–Barnes lemma for every weight of Section 4 (hypothesis (R))

One general Mellin–Barnes lemma serves all homogeneous weights: a weight `W_s(p,q) = q^{-L(s)} f_s(p/q)` whose `f_s` has the Mellin–Barnes representation
`f_s(t) = (1/2πi)∫_{(c)} k(z,s) t^{-z} dz` gives `∑_{p,q} W_s(p,q) = (1/2πi)∫_{(c)} k(z,s) P(z) P(L(s)-z) dz`, and with
a factor `log p log q` the same with `Q`. That is `tsum_eq_verticalIntegral'_of_mellin` below (the Fubini step of
`T_eq_verticalIntegral'_KerS`, with `k`, `f`, `L(s)` and the prime weight `ω` general; it also gives the absolute
convergence of the series, so no example needs its own convergence argument: `S`'s AM-GM step is not needed).

Every `f_s` here is `t^μ (1 + t^a)^{-ν}`, whose kernel is `kMB a μ ν = a⁻¹K_ν((z + μ)/a)`
(`mellinInv_kMB`, from `one_add_cpow_neg_eq_verticalIntegral'` by `u = t^a` and the affine change of variable
`z = aw - μ`, `verticalIntegral'_comp_affine`). Holomorphy of a double series on an open set is the Weierstrass
M-test (`differentiableOn_dser`).

No (Z6) here: the kernels' integrability on a line is the polynomial `Γ` decay (`integrable_KerS_line`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `verticalIntegral'_comp_affine`, `mellinInv_kMB`, `tsum_eq_verticalIntegral'_of_mellin`, `differentiableOn_dser`. -/

/-! ## Real lemmas -/

/-- `Dser` only sees the weight at pairs of primes. -/
lemma dser_congr {W W' : ℂ → ℕ → ℕ → ℂ} {s : ℂ}
    (h : ∀ pq : Nat.Primes × Nat.Primes, W s (pq.1 : ℕ) (pq.2 : ℕ) = W' s (pq.1 : ℕ) (pq.2 : ℕ)) :
    Dser W s = Dser W' s :=
  tsum_congr h

end GoldbachBoundaries.Paper2.M4b
