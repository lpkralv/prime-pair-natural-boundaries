import PrimePairNB.TIdentity.Basic

/-!
# `Γ Q` is integrable on vertical lines `Re z = σ > 1`

The two line-integrability helpers `continuous_Gamma_line` and `integrable_Gamma_mul_of_bound`
(shared with `G8c_IntegrableRH`) are in `Basic.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- On `Re z > 1`, every term of the Möbius series is regular, so `Qcont` is analytic there
(unconditional). -/
theorem analyticAt_Qcont_of_one_lt {z : ℂ} (hz : 1 < z.re) : AnalyticAt ℂ Qcont z := by
  have hz0 : 0 < z.re := by linarith
  have h := analyticAt_Qcont_sub_sum hz0 ∅ fun n _ hmu => by
    have hn0 : n ≠ 0 := (squarefree_of_mu_ne_zero hmu).ne_zero
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    apply ne_one_and_zeta_ne_zero_of_one_lt_re
    rw [re_natCast_mul]
    nlinarith
  simpa using h

/-- On `Re z = σ > 1`, `|Q(z)| ≤ ∑_p log p · p^{-σ}`. -/
theorem norm_Qcont_le_of_one_lt {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    ‖Qcont (σ + y * I)‖ ≤
      ∑' p : Nat.Primes, ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := by
  have hre : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
  have hterm : ∀ p : Nat.Primes,
      ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + y * I))‖ =
        ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := fun p => by
    rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos p.prop.pos,
      norm_natCast_cpow_of_pos p.prop.pos]
    simp
  rw [Qcont_eq_Q_of_one_lt hre, Q]
  refine le_trans (norm_tsum_le_tsum_norm ((summable_norm_Q_terms hre))) (le_of_eq ?_)
  exact tsum_congr hterm

/-- **`Γ Q` is integrable on vertical lines `Re z = σ > 1`** (unconditional; used for Mellin
inversion).

Proof sketch. On `Re z = σ > 1`, `Qcont = Q` (`hasSum_Q_moebius_zeta`; see the `EqOn` clause in
the proof of `lem_Sigma_i_ii_proof`) and `|Q(σ + iy)| ≤ ∑_p log p · p^{-σ}`
(`summable_norm_Q_terms`). `Γ(σ + iy)` decays like `(1 + |y|)^{-2}`
(`norm_Gamma_mul_one_add_abs_im_pow_le`). Measurability: the integrand is continuous in `y`
(`Q_differentiableOn`, `Complex.differentiableAt_Gamma`). -/
theorem integrable_Gamma_mul_Qcont_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    Integrable fun y : ℝ => Gamma (σ + y * I) * Qcont (σ + y * I) := by
  set K : ℝ := ∑' p : Nat.Primes, ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ with hKdef
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  refine integrable_Gamma_mul_of_bound (by linarith) ?_ (K := K) fun y => ?_
  · rw [continuous_iff_continuousAt]
    intro y
    have hre : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
    exact (analyticAt_Qcont_of_one_lt hre).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  · calc ‖Qcont (σ + y * I)‖ ≤ K := norm_Qcont_le_of_one_lt hσ y
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * (1 + |y|) := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg y]) hK0

end TIdentity

end GoldbachBoundaries
