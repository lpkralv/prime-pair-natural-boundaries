import PrimePairNB.TIdentity.Basic

/-!
# `Fw_continuousOn_and_le_exp`

The summability helper `summable_log_mul_exp_neg` (shared with `G9b_MellinFw`) is in `Basic.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- **Basic properties of `F`:** continuous on `t > 0`, and `F(t) ≤ C e^{-t}` for `t ≥ 1`
(a bound `C e^{-2t}` also holds; `e^{-t}` is all we use).

Proof sketch. For `t ≥ δ > 0`, `log p · e^{-pt} ≤ log p · e^{-pδ}`, summable over primes (e.g.
`log p ≤ p`, `∑ p e^{-pδ} < ∞`), so the series converges uniformly on `[δ, ∞)`
(`continuousOn_tsum` / Weierstrass M-test) and is continuous on `(0, ∞)`. For `t ≥ 1`,
`e^{-pt} = e^{-t} e^{-(p-1)t} ≤ e^{-t} e^{-(p-1)}`, so `F(t) ≤ e^{-t} ∑_p log p e^{1-p}`. -/
theorem Fw_continuousOn_and_le_exp :
    ContinuousOn Fw (Ioi 0) ∧ ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → Fw t ≤ C * Real.exp (-t) := by
  have hlog : ∀ p : Nat.Primes, 0 ≤ Real.log (p : ℕ) := fun p =>
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  refine ⟨fun t ht => ?_, ?_⟩
  · have ht' : 0 < t / 2 := by have := mem_Ioi.mp ht; linarith
    have hcont : ContinuousOn Fw (Ioi (t / 2)) := by
      refine continuousOn_tsum (fun p => by fun_prop) (summable_log_mul_exp_neg ht')
        fun p x hx => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (hlog p) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hlog p)
      have hx' : t / 2 < x := hx
      have : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
      nlinarith
    have hmem : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by have := mem_Ioi.mp ht; linarith)
    exact (hcont.continuousAt hmem).continuousWithinAt
  · refine ⟨Real.exp 1 * ∑' p : Nat.Primes, Real.log (p : ℕ) * Real.exp (-((p : ℕ) * 1)),
      fun t ht => ?_⟩
    have hs1 := summable_log_mul_exp_neg (δ := 1) one_pos
    have hst := summable_log_mul_exp_neg (δ := t) (by linarith)
    rw [show Real.exp 1 * (∑' p : Nat.Primes, Real.log (p : ℕ) * Real.exp (-((p : ℕ) * 1))) *
        Real.exp (-t) = ∑' p : Nat.Primes, Real.exp (-t) * (Real.exp 1 *
          (Real.log (p : ℕ) * Real.exp (-((p : ℕ) * 1)))) by
      rw [tsum_mul_left, tsum_mul_left]; ring]
    refine Summable.tsum_le_tsum (fun p => ?_) hst ((hs1.mul_left _).mul_left _)
    have hp : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_lt.le
    calc Real.log (p : ℕ) * Real.exp (-((p : ℕ) * t))
        ≤ Real.log (p : ℕ) * Real.exp (-t + 1 + -((p : ℕ) * 1)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (hlog p)
      _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

end TIdentity

end GoldbachBoundaries
