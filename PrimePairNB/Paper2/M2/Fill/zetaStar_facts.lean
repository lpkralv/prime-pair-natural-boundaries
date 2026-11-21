import PrimePairNB.Paper2.M2.QCount
import PrimePairNB.Paper2.M2.Fill.rep_facts

noncomputable section
open Complex ComplexConjugate
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The zero `ζ*`** (Z1). With `rep_facts`: if `q < k`, `ζ* = ρ'`, `Re = k/(2q) > 1/2`, `j = k`; if `k < q`,
`ζ* = 1 - ρ̄'` is a zero by (Z1), `Re = (2q - k)/(2q) > 1/2`, `j = 2q - k`, `Im = Im ρ'`. In both cases
`0 < Im ζ* = kγ/q < 2γ` (`γ > 0`, `k < 2q`), `q < j < 2q` and `gcd(j, q) = gcd(k, q) = 1`
(`Nat.Coprime` of `2q - k` from `(2q - k) + k = 2q`: `Nat.coprime_sub_self_left` or by `Nat.Coprime.gcd_eq_one`
and `Nat.gcd_sub_self_left`). -/
theorem zetaStar_facts (hZ1 : Z1) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {q : ℕ} (hq : q.Prime) {ρ' : ℂ} {k : ℕ} (hrep : IsRep (ρ / (q : ℂ)) ρ' k)
    (hne : (ρ', k) ≠ (ρ, q)) :
    zetaStar ρ' k q ∈ NontrivialZeros ∧ 1 / 2 < (zetaStar ρ' k q).re ∧
      0 < (zetaStar ρ' k q).im ∧ (zetaStar ρ' k q).im < 2 * ρ.im ∧
      ∃ j : ℕ, q < j ∧ j < 2 * q ∧ Nat.Coprime j q ∧ (zetaStar ρ' k q).re = (j : ℝ) / (2 * q) := by
  obtain ⟨hc, hk1, hk2, hkq, hr, hi⟩ := rep_facts hρ hre hq hrep hne
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2R : (k : ℝ) < 2 * q := by exact_mod_cast hk2
  have hi0 : 0 < ρ'.im := by rw [hi]; positivity
  have hi2 : ρ'.im < 2 * ρ.im := by
    rw [hi, div_lt_iff₀ hqR]
    nlinarith
  by_cases hqk : q < k
  · simp only [zetaStar, if_pos hqk]
    refine ⟨hrep.1, ?_, hi0, hi2, k, hqk, hk2, hc, hr⟩
    rw [hr, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)]
    have : (q : ℝ) < k := by exact_mod_cast hqk
    linarith
  · have hkq' : k < q := by omega
    have hkqR : (k : ℝ) < q := by exact_mod_cast hkq'
    have hsub : ((2 * q - k : ℕ) : ℝ) = 2 * q - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
    have hc' : Nat.Coprime (2 * q - k) q := by
      apply Nat.Coprime.symm
      apply hq.coprime_iff_not_dvd.mpr
      intro hd
      have hd' : q ∣ k := by
        have : q ∣ (2 * q - k) + k := by rw [Nat.sub_add_cancel (by omega)]; exact dvd_mul_left q 2
        exact (Nat.dvd_add_iff_right hd).mpr this
      exact (hq.coprime_iff_not_dvd.mp hc.symm) hd'
    simp only [zetaStar, if_neg hqk, sub_re, one_re, conj_re, sub_im, one_im, conj_im, sub_neg_eq_add, zero_add]
    refine ⟨(hZ1 ρ' hrep.1).2.1, ?_, hi0, hi2, 2 * q - k, by omega, by omega, hc', ?_⟩
    · rw [hr]
      have hh : (k : ℝ) / (2 * q) < 1 / 2 := by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
        nlinarith
      linarith
    · rw [hsub, hr]
      field_simp
end GoldbachBoundaries.Paper2.M2
