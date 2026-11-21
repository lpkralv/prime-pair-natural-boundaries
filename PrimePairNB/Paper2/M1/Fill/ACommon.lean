import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma A_ordZeta_eq_zero_of_one_lt {w : ℂ} (hw : 1 < w.re) : ordZeta w = 0 := by
  have h1 : w ≠ 1 := fun h => by simp [h] at hw
  have hz : w ∉ NontrivialZeros := fun h => by linarith [h.2.2]
  simp [ordZeta, h1, hz]

lemma A_hasResidue_A {w : ℂ} (hw : 0 < w.re) :
    HasResidue negLogDerivZeta w (-(ordZeta w : ℂ)) := by
  by_cases h1 : w = 1
  · subst w
    simpa [ordZeta] using hasResidue_negLogDerivZeta_one
  by_cases hz : w ∈ NontrivialZeros
  · simpa [ordZeta, h1, hz] using hasResidue_negLogDerivZeta_of_ne_one h1
  have hn : riemannZeta w ≠ 0 := by
    intro h
    have hlt : w.re < 1 := lt_of_not_ge fun hle => riemannZeta_ne_zero_of_one_le_re hle h
    exact hz ⟨h, hw, hlt⟩
  simpa [ordZeta, h1, hz] using hasResidue_zero_of_analyticAt (analyticAt_negLogDerivZeta h1 hn)

lemma A_hasResidue_term {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    HasResidue (sigmaTerm n) a (- (mu n / n * (ordZeta ((n : ℂ) * a) : ℂ))) := by
  by_cases hn : n = 0
  · subst n
    rw [sigmaTerm_of_mu_eq_zero (by simp [mu])]; simpa using (hasResidue_zero (a := a))
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := ((A_hasResidue_A (w := (n : ℂ) * a) (by simpa using mul_pos hnR ha)).comp_natCast_mul
    (by omega : 1 ≤ n)).const_mul (mu n)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [mul_div_cancel_left₀ a hnC] at h
  convert h using 1 <;> first | rfl | ring

/-- Finite linearity for the punctured-limit residue used in this directory. -/
lemma A_hasResidue_sum {a : ℂ} (ha : 0 < a.re) (S : Finset ℕ) :
    HasResidue (fun z => ∑ n ∈ S, sigmaTerm n z) a
      (- ∑ n ∈ S, mu n / n * (ordZeta ((n : ℂ) * a) : ℂ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (hasResidue_zero (a := a))
  | @insert n S hn ih =>
    simpa [Finset.sum_insert hn, neg_add, add_comm] using (A_hasResidue_term ha n).add' ih

lemma A_Rcoef_eq_sum {a : ℂ} (M : ℕ)
    (hout : ∀ n, M ≤ n → 1 < ((n : ℂ) * a).re) :
    Rcoef a = -∑ n ∈ Finset.range M, mu n / n * (ordZeta ((n : ℂ) * a) : ℂ) := by
  unfold Rcoef
  congr 1
  rw [tsum_eq_sum (s := Finset.range M)]
  · have hlast : mu M / (M : ℂ) * (ordZeta ((M : ℂ) * a) : ℂ) = 0 := by
      rw [A_ordZeta_eq_zero_of_one_lt (hout M le_rfl)]; simp
    have hzero : mu 0 / (0 : ℂ) * (ordZeta ((0 : ℂ) * a) : ℂ) = 0 := by simp
    have hs := Finset.sum_range_succ' (fun n : ℕ => mu n / (n : ℂ) * (ordZeta ((n : ℂ) * a) : ℂ)) M
    rw [Finset.sum_range_succ, hlast] at hs
    simpa using hs.symm
  · intro n hn
    have hnM : M ≤ n := by simpa using hn
    rw [A_ordZeta_eq_zero_of_one_lt (hout (n + 1) (by omega))]; simp

/-- A residue formula valid at every point of the open right half-plane. -/
lemma A_hasResidue_Qcont {a : ℂ} (ha : 0 < a.re) : HasResidue Qcont a (Rcoef a) := by
  obtain ⟨M, _, hM⟩ := exists_tail_index ha 1
  have hout : ∀ n, M ≤ n → 1 < ((n : ℂ) * a).re := by
    intro n hn
    have hnR : (M : ℝ) ≤ n := by exact_mod_cast hn
    simp only [re_natCast_mul]
    nlinarith
  have han := analyticAt_Qcont_sub_sum ha (Finset.range M) (fun n hn _ =>
    ne_one_and_zeta_ne_zero_of_one_lt_re (hout n (by simpa using hn)))
  have hr := (A_hasResidue_sum ha (Finset.range M)).add_analyticAt han
  have heq := A_Rcoef_eq_sum M hout
  rw [heq]
  exact hr.congr (Eventually.of_forall fun z => by simp)

end GoldbachBoundaries.Paper2.M1
