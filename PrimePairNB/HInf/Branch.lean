import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch
import PrimePairNB.HInf.Fill.pinch_countable
import PrimePairNB.HInf.Fill.Pth_local
import PrimePairNB.HInf.Fill.add_mem_Uth
import PrimePairNB.HInf.Fill.hasDerivAt_Pth
import PrimePairNB.HInf.Fill.isOpen_Uth
import PrimePairNB.HInf.Fill.norm_Pth_le

/-!
# HInf: the branch `P^θ`

`Pth` is the explicit formula of `Defs.lean`; the first group of lemmas is unconditional.

`norm_Pth_le`: the premise is (Z3) (Titchmarsh Thm 9.6(A)); the bound comes from `Paper2.M1.norm_Qcont_le_growth` (Z1, Z2, Z3) in a few lines: on `z + 2τ·slantDir κ` the
real part only grows, `|Im|` changes by at most `2|κ|`, and `|P(z + 2 slantDir κ)| ≤ P(2)`. So (Z3) is a named premise;
it could be replaced by a Borel–Carathéodory argument on `log ζ`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Lemma 5.1.** If `a` is the only point of `Σ` on its `κ`-line, then for small `R`, off the cut,
`P^θ(z) = c(a) Log_θ(z - a) + E_a(z)` with `E_a` holomorphic on the disc, and the slit disc lies in `U_θ`. -/
theorem Pth_local {κ : ℝ} {a : ℂ} (ha : a ∈ PoleSetQ)
    (hsole : ∀ a' ∈ PoleSetQ, a' ≠ a → ∀ t : ℝ, a' - a ≠ (t : ℂ) * slantDir κ) :
    ∃ R : ℝ, 0 < R ∧ ball a R ⊆ halfPlane 0 ∧ ball a R \ rayW κ a ⊆ Uth κ ∧
      ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball a R) ∧
        ∀ z ∈ ball a R \ rayW κ a, Pth κ z = cP a * logK κ (z - a) + E z :=
  @Fill.Pth_local κ a ha hsole

/-- **Paper, Lemma 5.1.** For `η > 0` there are `T`, `C` with `z ∈ U_θ` and `|P^θ(z)| ≤ C log(|Im z| + 2)` on
`Re z ≥ B_∞ + 2η`, `|Im z| ≥ T`. Premises (Z1), (Z2), (Z3): (Z3) stands in place of the Borel–Carathéodory argument. -/
theorem norm_Pth_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (κ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T C : ℝ, ∀ z : ℂ, Binf + 2 * η ≤ z.re → T ≤ |z.im| →
      z ∈ Uth κ ∧ ‖Pth κ z‖ ≤ C * Real.log (|z.im| + 2) :=
  @Fill.norm_Pth_le hZ1 hZ2 hZ3 κ η hη

end GoldbachBoundaries.HInf
