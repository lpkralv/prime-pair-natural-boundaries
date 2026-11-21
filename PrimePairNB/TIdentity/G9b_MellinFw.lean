import PrimePairNB.TIdentity.G9a_FwBasic

/-!
# `mellin_Fw`

Uses the general lemma `mellin_convergent_and_hasSum_of_exp` (in `Basic.lean`, shared by `G9b_MellinFw`
and `G9c_MellinFwSq`), which adds convergence (`MellinConvergent`) to
Mathlib's `hasSum_mellin` (`Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean`, Apache-2.0,
David Loeffler); the integrability and summability steps are copied from that proof.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- **Mellin transform of `F`** (`Γ(z)Q(z) = ∫_0^∞ F(t) t^{z-1} dt`,
`Re z > 1`), with convergence.

Proof sketch. Tonelli/Fubini for the sum over primes and the integral
(`integral_tsum_of_summable_integral_norm`, or `MeasureTheory.integral_tsum`), with
`∫_0^∞ e^{-pt} t^{z-1} dt = Γ(z) p^{-z}` (`Complex.Gamma_eq_integral`,
`Complex.GammaIntegral`, substitution `u = pt`: `integral_comp_mul_left_Ioi`). Summability of the
norms: `∑_p log p · Γ(Re z) p^{-Re z} < ∞` (`summable_norm_Q_terms`). Then `Q z` is the `tsum`. -/
theorem mellin_Fw {z : ℂ} (hz : 1 < z.re) :
    MellinConvergent (fun t => (Fw t : ℂ)) z ∧ mellin (fun t => (Fw t : ℂ)) z = Gamma z * Q z := by
  have hz0 : 0 < z.re := by linarith
  have hw : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.prop.pos
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun p : Nat.Primes ↦
      (Real.log (p : ℕ) : ℂ) * Real.exp (-((p : ℕ) : ℝ) * t)) (Fw t : ℂ) := fun t ht ↦ by
    have h := (summable_log_mul_exp_neg (mem_Ioi.mp ht)).hasSum
    rw [← Complex.hasSum_ofReal] at h
    convert h using 1
    · funext p
      push_cast
      ring_nf
    · rfl
  have hFc : ContinuousOn (fun t => (Fw t : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn Fw_continuousOn_and_le_exp.1
  have hnorm : ∀ p : Nat.Primes, ‖(Real.log (p : ℕ) : ℂ)‖ / ((p : ℕ) : ℝ) ^ z.re =
      ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ := fun p ↦ by
    rw [norm_mul, norm_natCast_cpow_of_pos p.prop.pos, neg_re, Real.rpow_neg (Nat.cast_nonneg _),
      div_eq_mul_inv]
  have h_sum : Summable fun p : Nat.Primes ↦
      ‖(Real.log (p : ℕ) : ℂ)‖ / ((p : ℕ) : ℝ) ^ z.re := by
    simp_rw [hnorm]; exact summable_norm_Q_terms hz
  obtain ⟨hconv, hval⟩ := mellin_convergent_and_hasSum_of_exp hw hz0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, Q, ← tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [ofReal_natCast, cpow_neg, mul_div_assoc, div_eq_mul_inv]

end TIdentity

end GoldbachBoundaries
