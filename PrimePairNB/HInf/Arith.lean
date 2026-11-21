import PrimePairNB.HInf.Kernels
import PrimePairNB.HInf.Fill.bracketK_ne_zero
import PrimePairNB.HInf.Fill.far_tail_S
import PrimePairNB.HInf.Fill.norm_KS_le
import PrimePairNB.HInf.Fill.pairSumS_ne_zero_of_not_nearBad
import PrimePairNB.HInf.Fill.prop71_S
import PrimePairNB.HInf.Fill.prop71_joint

/-!
# HInf: far pairs and non-vanishing

For `G` this is already proved: `Paper2.M2.prop_Lambda_proof` gives `Σ_G ≠ 0`, under (Z1), (Z2), (Z4), (Z5), (Z6)
and `B < 1`. The single-representation result is `Paper2.M2.thm_single_proof`, and its "near-bad" set is `Paper2.M2.NearBad`.

For `S` the kernel differs and the bound is re-derived. `H = 2 log X` still works: the far sum is
`≤ e^{-H} = X^{-2}` against a main term `≫ 1/X`, which is weaker than the `X^{-π + o(1)}` available for `G` and enough.
Reuse for `S`: `Paper2.M2.thm_single_proof`, `SH_finite_ncard_le`, `nearBad_finite_ncard_le`, `eventually_nearBad_small`,
`ncard_far_shell_le`, `summable_tsum_le_of_shells`, and `prop_Lambda_of_core` as a template.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- The bracket of the main term of `S` is non-zero off the real axis: `K(1 - u/4) + K(1/2 + u/4) ≠ 0`, as `cot πw = 4w`
has no non-real solution.  -/
theorem bracketK_ne_zero {u : ℂ} (hu : u.im ≠ 0) : KS (1 - u / 4) + KS (1 / 2 + u / 4) ≠ 0 :=
  @Fill.bracketK_ne_zero u hu

/-- **Far pairs for `K`**, the analogue of `Paper2.lem_far` with `KS ((a - b + 3)/4)` for `betaB a b`. No (Z6). -/
theorem far_tail_S (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)‖ ≤ Real.exp (-H) :=
  @Fill.far_tail_S hZ1 hZ2 hB Y hY

/-- **Joint form**: one family of good points (`IsSingleRep ρ q`), both sums non-zero. The boundary theorem uses each sum separately, so this
joint form is not on the path to `boundary_GS` (`prop71_G`, `prop71_S` are). Paper, Theorem 3.1. -/
theorem prop71_joint (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      IsSingleRep ρ q ∧ s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0 ∧ pairSumS s₀ ≠ 0}.Infinite :=
  @Fill.prop71_joint hZ1 hZ2 hZ4 hZ5 hZ6 hB y ε hε

end GoldbachBoundaries.HInf
