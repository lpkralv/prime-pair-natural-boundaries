import PrimePairNB.TIdentity.G9a_FwBasic

/-!
# `mellin_Fw_sq`

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

/-- **Mellin transform of `F²`** (`Γ(s)T(s) = ∫_0^∞ F(t)² t^{s-1} dt`,
`Re s > 2`), with convergence.

Proof sketch. As `mellin_Fw`, over pairs of primes: `F(t)² = ∑_{p,q} log p log q e^{-(p+q)t}`
(product of two absolutely convergent series, `tsum_mul_tsum_of_summable_norm`, indexed by
`Nat.Primes × Nat.Primes` as in the definition of `T`), and
`∫_0^∞ e^{-(p+q)t} t^{s-1} dt = Γ(s)(p+q)^{-s}`. Summability: `∑_{p,q} log p log q (p+q)^{-σ}
≤ ∑_{p,q} log p log q (pq)^{-σ/2} < ∞` for `σ > 2` (AM-GM `p + q ≥ 2√(pq)`). -/
theorem mellin_Fw_sq {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (fun t => ((Fw t ^ 2 : ℝ) : ℂ)) s ∧
      mellin (fun t => ((Fw t ^ 2 : ℝ) : ℂ)) s = Gamma s * T s := by
  set σ := s.re with hσ
  have hs0 : 0 < σ := by linarith
  have hlog : ∀ p : Nat.Primes, 0 ≤ Real.log (p : ℕ) := fun p =>
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hpos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.prop.pos
  set a : Nat.Primes × Nat.Primes → ℂ :=
    fun pq => (Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) with ha
  set w : Nat.Primes × Nat.Primes → ℝ := fun pq => ((pq.1 : ℕ) : ℝ) + ((pq.2 : ℕ) : ℝ) with hwdef
  have hw : ∀ pq, 0 < w pq := fun pq => add_pos (hpos _) (hpos _)
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun pq ↦ a pq * Real.exp (-w pq * t))
      ((Fw t ^ 2 : ℝ) : ℂ) := fun t ht ↦ by
    have hf := summable_log_mul_exp_neg (mem_Ioi.mp ht)
    have hnn : ∀ p : Nat.Primes, 0 ≤ Real.log (p : ℕ) * Real.exp (-((p : ℕ) * t)) := fun p =>
      mul_nonneg (hlog p) (Real.exp_pos _).le
    have hprod := hf.hasSum.mul hf.hasSum (hf.mul_of_nonneg hf hnn hnn)
    rw [← Complex.hasSum_ofReal] at hprod
    convert hprod using 1
    · funext pq
      simp only [ha, hwdef]
      rw [show -(((pq.1 : ℕ) : ℝ) + ((pq.2 : ℕ) : ℝ)) * t =
        -(((pq.1 : ℕ) : ℝ) * t) + -(((pq.2 : ℕ) : ℝ) * t) by ring, Real.exp_add]
      push_cast
      ring
    · rw [sq]; rfl
  have hFc : ContinuousOn (fun t => ((Fw t ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn (Fw_continuousOn_and_le_exp.1.pow 2)
  -- summability: `(p + q)^σ ≥ (pq)^{σ/2}`
  have key : ∀ x y : ℝ, 0 < x → 0 < y → x ^ (σ / 2) * y ^ (σ / 2) ≤ (x + y) ^ σ := by
    intro x y hx hy
    calc x ^ (σ / 2) * y ^ (σ / 2) = (x * y) ^ (σ / 2) := (Real.mul_rpow hx.le hy.le).symm
      _ ≤ ((x + y) ^ (2 : ℝ)) ^ (σ / 2) :=
          Real.rpow_le_rpow (by positivity) (by rw [Real.rpow_two]; nlinarith) (by linarith)
      _ = (x + y) ^ σ := by rw [← Real.rpow_mul (by positivity)]; ring_nf
  set g : Nat.Primes → ℝ := fun p => Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ (σ / 2) with hg
  have hg_sum : Summable g := by
    have h := summable_norm_Q_terms (z := ((σ / 2 : ℝ) : ℂ)) (by simp only [ofReal_re]; linarith)
    refine h.congr fun p => ?_
    rw [norm_mul, norm_natCast_cpow_of_pos p.prop.pos, neg_re, ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg _), Complex.norm_real, Real.norm_of_nonneg (hlog p),
      div_eq_mul_inv]
    simp only [hg, div_eq_mul_inv]
  have hg_nn : 0 ≤ g := fun p => div_nonneg (hlog p) (by positivity)
  have h_sum : Summable fun pq ↦ ‖a pq‖ / (w pq) ^ σ := by
    refine (hg_sum.mul_of_nonneg hg_sum hg_nn hg_nn).of_nonneg_of_le
      (fun pq => div_nonneg (norm_nonneg _) (by have := hw pq; positivity)) fun pq => ?_
    simp only [ha, hwdef, hg]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hlog _),
      Real.norm_of_nonneg (hlog _), div_mul_div_comm]
    exact div_le_div_of_nonneg_left (mul_nonneg (hlog _) (hlog _))
      (by have := hpos pq.1; have := hpos pq.2; positivity) (key _ _ (hpos _) (hpos _))
  obtain ⟨hconv, hval⟩ := mellin_convergent_and_hasSum_of_exp hw hs0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, T, ← tsum_mul_left]
  refine tsum_congr fun pq ↦ ?_
  have hcast : ((w pq : ℝ) : ℂ) = ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ)) : ℂ) := by
    simp only [hwdef]; push_cast; ring
  rw [hcast, cpow_neg, mul_div_assoc, div_eq_mul_inv]

end TIdentity

end GoldbachBoundaries
