import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `R_a` is real and `R_{ā} = R_a` (Z1: `m(k ā) = m(k a)`). Each term of the sum defining `R_a` is real; only finitely many
are non-zero. Uses: `conj_mem_poleSetQ`. -/
theorem Rcoef_real_conj (hZ1 : Z1) {a : ℂ} (ha : a ∈ PoleSetQ) :
    (Rcoef a).im = 0 ∧ Rcoef (conj a) = Rcoef a := by
  classical
  have hreal : conj (Rcoef a) = Rcoef a := by
    simp only [Rcoef, map_neg, Complex.conj_tsum]
    congr 1
    apply tsum_congr
    intro k
    simp [map_mul, map_div]
  refine ⟨Complex.conj_eq_iff_im.mp hreal, ?_⟩
  have hord : ∀ w : ℂ, ordZeta (conj w) = ordZeta w := by
    intro w
    have hmem : conj w ∈ NontrivialZeros ↔ w ∈ NontrivialZeros :=
      ⟨fun h => by simpa using conj_mem_nontrivialZeros h, conj_mem_nontrivialZeros⟩
    by_cases hw : w = 1
    · simp [hw]
    have hwconj : conj w ≠ 1 := by
      intro h
      apply hw
      have hc := congrArg (conj : ℂ → ℂ) h
      simpa using hc
    by_cases hz : w ∈ NontrivialZeros
    · simp [ordZeta, hw, hwconj, hmem, (hZ1 w hz).1.2]
    · simp [ordZeta, hw, hwconj, hmem, hz]
  unfold Rcoef
  congr 1
  apply tsum_congr
  intro k
  have heq : (((k + 1 : ℕ) : ℂ) * conj a) = conj (((k + 1 : ℕ) : ℂ) * a) := by simp
  rw [heq, hord]

end GoldbachBoundaries.Paper2.M1
