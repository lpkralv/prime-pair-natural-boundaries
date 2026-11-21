import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.BCommon

/-! `norm_sigmaTail_two_le`. Terms `k ≥ 4` by `norm_sigmaTerm_le` with `d = 1/2`
(geometric); terms `k = 2, 3` by `‖A(s)‖ ≤ ∑ Λ(m) m^{-(1+4δ)}` on `Re s ≥ 1 + 4δ`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The tail `∑_{k ≥ 2} μ(k) A(k w)` is bounded** on `Re w ≥ 1/2 + 2δ` (`Re(kw) ≥ 1 + 4δ`; for large `k`,
`norm_sigmaTerm_le`; the finitely many small `k` by `|A(x+iy)| ≤ A(x)` for `x > 1`). -/
theorem norm_sigmaTail_two_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 + 2 * δ ≤ w.re → ‖sigmaTail 2 w‖ ≤ C := by
  set K := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 + 4 * δ)) with hKdef
  set b : ℕ → ℝ := fun m =>
    (if m < 2 then K else 0) + vmConst * 4 * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (m + 2) with hbdef
  have hb : Summable b := by
    refine Summable.add ?_ (summable_tail_bound (by norm_num) 2)
    refine summable_of_ne_finset_zero (s := Finset.range 2) fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp [hm]
  refine ⟨∑' m, b m, fun w hw => ?_⟩
  refine tsum_of_norm_bounded hb.hasSum fun m => ?_
  have hgeom : 0 ≤ vmConst * 4 * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (m + 2) := by
    have := vmConst_nonneg
    positivity
  by_cases hm : m < 2
  · simp only [hbdef, hm, ↓reduceIte]
    have hre : 1 + 4 * δ ≤ (((m + 2 : ℕ) : ℂ) * w).re := by
      rw [re_natCast_mul]
      have h2 : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
        push_cast
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      nlinarith
    calc ‖sigmaTerm (m + 2) w‖ ≤ 1 * ‖negLogDerivZeta (((m + 2 : ℕ) : ℂ) * w)‖ := by
          rw [sigmaTerm, norm_mul]
          gcongr
          exact norm_mu_le_one _
      _ ≤ K := by
          rw [one_mul]
          exact norm_negLogDerivZeta_le_of_re (by linarith) hre
      _ ≤ _ := le_add_of_nonneg_right hgeom
  · simp only [hbdef, hm, ↓reduceIte, zero_add]
    refine norm_sigmaTerm_le ?_ (by linarith)
    have : (2 : ℝ) ≤ m := by exact_mod_cast (not_lt.mp hm)
    push_cast
    linarith

end GoldbachBoundaries.Paper2.M1
