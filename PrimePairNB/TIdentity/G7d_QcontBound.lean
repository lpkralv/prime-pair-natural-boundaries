import PrimePairNB.TIdentity.G7c_LogDerivZetaBound

/-!
# The growth bound for `Q`. Under RH, `‖Qcont z‖ ≤ C_ε log |Im z|` on `Re z ≥ 1/2 + ε`, `|Im z| ≥ 4`

Proof. Put `d = 1/2 + ε` and pick `N ≥ 2` with `N d ≥ 2` (`exists_tail_index`). Split
`Qcont z = ∑_{n < N} μ(n) A(n z) + tail_N(z)` (`Qcont_eq_sum_add_tail`).
* `n = 1`: `A(z)`, bounded by `C₀ log |y|` (`norm_negLogDerivZeta_le_log`).
* `n = 0`: the term is `0` (`μ(0) = 0`).
* `2 ≤ n < N`: `Re(n z) ≥ 2d = 1 + 2ε`, so `‖A(n z)‖ ≤ B = ∑_m ‖Λ(m) m^{-(1+2ε)}‖` (termwise
  comparison of the absolutely convergent L-series, `norm_negLogDerivZeta_le_of_re`).
* tail: `≤ T = ∑_m 4 C_Λ (2^{-d})^{m+N}` (`norm_sigmaTerm_le`).
So `‖Qcont z‖ ≤ C₀ log |y| + N B + T ≤ (C₀ + N B + T) log |y|`, since `log |y| ≥ log 4 > 1`.
-/

noncomputable section

open Complex Set Metric ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

namespace TIdentity

/-- `‖A(w)‖ ≤ ∑_m ‖Λ(m) m^{-σ₀}‖` on `Re w ≥ σ₀ > 1`. -/
lemma norm_negLogDerivZeta_le_of_re {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {w : ℂ} (hw : σ₀ ≤ w.re) :
    ‖negLogDerivZeta w‖ ≤ ∑' n, ‖term ↗Λ (σ₀ : ℂ) n‖ := by
  rw [negLogDerivZeta_eq_LSeries (by linarith), LSeries]
  have hs : LSeriesSummable ↗Λ (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ₀)
  exact tsum_of_norm_bounded (summable_norm_iff.mpr hs).hasSum
    (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hw) n)

/-- **The growth bound for `Q`:** under RH, `|Q(x + iy)| ≤ C_ε log |y|` for
`x ≥ 1/2 + ε`, `|y| ≥ 4`, with `Q` continued by `Qcont`.

Proof sketch. `Qcont z = A(z) + ∑_{n ≥ 2} μ(n) A(n z)` (`Qcont` is a `tsum` over `n`, the `n = 0`
term is `0`, `summable_sigmaTerm`). The first term is `norm_negLogDerivZeta_le_log`. For `n ≥ 2`,
`Re(n z) ≥ 1 + 2ε`, so `|A(n z)| ≤ ∑_m Λ(m) m^{-(1+2ε)}` (absolute convergence), and for
`n (1/2 + ε) ≥ 2` the geometric bound `norm_sigmaTerm_le` applies; the sum over `n ≥ 2` is bounded
uniformly in `y`. Absorb the constant using `log |y| ≥ log 4 > 1`. -/
theorem norm_Qcont_le_log (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z : ℂ, 1 / 2 + ε ≤ z.re → 4 ≤ |z.im| → ‖Qcont z‖ ≤ C * Real.log |z.im| := by
  obtain ⟨C₀, hC₀⟩ := norm_negLogDerivZeta_le_log hRH hε
  set d : ℝ := 1 / 2 + ε with hd
  have hd0 : 0 < d := by positivity
  obtain ⟨N, hN2, hN⟩ := exists_tail_index hd0 2
  set σ₀ : ℝ := 1 + 2 * ε with hσ₀def
  have hσ₀ : 1 < σ₀ := by linarith
  set B : ℝ := ∑' n, ‖term ↗Λ (σ₀ : ℂ) n‖ with hBdef
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  set T : ℝ := ∑' m : ℕ, vmConst * 4 * ((2 : ℝ) ^ (-d)) ^ (m + N) with hTdef
  have hT : 0 ≤ T := tsum_nonneg fun m => by have := vmConst_nonneg; positivity
  refine ⟨C₀ + N * B + T, fun z hre him => ?_⟩
  have hz0 : 0 < z.re := by linarith
  have hlog4 : 1 < Real.log 4 := by
    have := Real.exp_one_lt_d9
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith
  have hlogy : 1 ≤ Real.log |z.im| := le_trans hlog4.le (Real.log_le_log (by norm_num) him)
  rw [Qcont_eq_sum_add_tail N hz0]
  have htail : ‖sigmaTail N z‖ ≤ T :=
    tsum_of_norm_bounded (summable_tail_bound hd0 N).hasSum
      (fun m => norm_sigmaTerm_le (two_le_shift hd0 hN m) hre)
  have hterm : ∀ n ∈ (Finset.range N).erase 1, ‖sigmaTerm n z‖ ≤ B := by
    intro n hn
    have hn1 : n ≠ 1 := Finset.ne_of_mem_erase hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 0 := by omega
      subst this
      simp [sigmaTerm, mu, hB]
    · have hre' : σ₀ ≤ ((n : ℂ) * z).re := by
        rw [re_natCast_mul]
        have : (2 : ℝ) ≤ n := by exact_mod_cast h
        have : 2 * d ≤ n * z.re := by nlinarith
        linarith
      calc ‖sigmaTerm n z‖ ≤ 1 * ‖negLogDerivZeta (n * z)‖ := by
            rw [sigmaTerm, norm_mul]; gcongr; exact norm_mu_le_one n
        _ ≤ B := by rw [one_mul]; exact norm_negLogDerivZeta_le_of_re hσ₀ hre'
  have hsum : ‖∑ n ∈ (Finset.range N).erase 1, sigmaTerm n z‖ ≤ N * B := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
    have : (((Finset.range N).erase 1).card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_erase_le).trans (Finset.card_range N).le
    exact mul_le_mul_of_nonneg_right this hB
  have h1mem : 1 ∈ Finset.range N := by simp; omega
  rw [← Finset.add_sum_erase _ _ h1mem]
  have hs1 : sigmaTerm 1 z = negLogDerivZeta z := by simp [sigmaTerm, mu]
  rw [hs1]
  have hA := hC₀ z hre him
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  calc ‖negLogDerivZeta z + ∑ n ∈ (Finset.range N).erase 1, sigmaTerm n z + sigmaTail N z‖
      ≤ ‖negLogDerivZeta z‖ + ‖∑ n ∈ (Finset.range N).erase 1, sigmaTerm n z‖ +
          ‖sigmaTail N z‖ := norm_add₃_le
    _ ≤ C₀ * Real.log |z.im| + N * B + T := by gcongr
    _ ≤ C₀ * Real.log |z.im| + (N * B) * Real.log |z.im| + T * Real.log |z.im| := by
        have h1 := le_mul_of_one_le_right hNB hlogy
        have h2 := le_mul_of_one_le_right hT hlogy
        linarith
    _ = (C₀ + N * B + T) * Real.log |z.im| := by ring

end TIdentity
end GoldbachBoundaries
