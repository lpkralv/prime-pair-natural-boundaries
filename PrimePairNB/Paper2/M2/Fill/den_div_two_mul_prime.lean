import PrimePairNB.Paper2.M2.QCount

noncomputable section
namespace GoldbachBoundaries.Paper2.M2

private lemma A_den_coprime (a b : ℕ) (hb : 0 < b) (hc : Nat.Coprime a b) :
    ((a : ℚ) / b).den = b := by
  have h := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ))
    (by exact_mod_cast hb) (by simpa using hc)
  have h' : (((a : ℚ) / (b : ℚ)).den : ℤ) = (b : ℤ) := by
    simpa only [Int.cast_natCast] using h
  exact Int.ofNat_inj.mp h'

/-- **The reduced denominator of `j/(2q)`** (elementary). For `q` prime, `q < j < 2q`, `gcd(j, q) = 1`: the reduced
denominator `d` of `j/(2q)` is `2q / gcd(j, 2q)` with `gcd(j, 2q) = gcd(j, 2)` (`Rat.den_div_eq_of_coprime` after
dividing out the gcd, or `Rat.divInt` lemmas). If `j` is odd, `d = 2q` (even, `d/2 = q`). If `j` is even then
`q ≠ 2` (for `q = 2` the only `j` is `3`), so `q` is odd and `d = q` (odd). -/
theorem den_div_two_mul_prime {q j : ℕ} (hq : q.Prime) (hj1 : q < j) (hj2 : j < 2 * q)
    (hcop : Nat.Coprime j q) :
    (((j : ℚ) / (2 * q)).den = q ∨ ((j : ℚ) / (2 * q)).den = 2 * q) ∧
      qOfDen ((j : ℚ) / (2 * q)).den = q := by
  rcases Nat.even_or_odd j with hj | hj
  · obtain ⟨m, hm⟩ := hj
    have hjm : j = 2 * m := by omega
    have hmq : Nat.Coprime m q := Nat.Coprime.of_dvd_left (hjm ▸ dvd_mul_left m 2) hcop
    have hqodd : Odd q := hq.odd_of_ne_two (by intro h; subst q; omega)
    have heq : (j : ℚ) / (2 * q) = (m : ℚ) / q := by rw [hjm]; push_cast; ring
    have hd : ((j : ℚ) / (2 * q)).den = q := by rw [heq]; exact A_den_coprime m q hq.pos hmq
    exact ⟨Or.inl hd, by simp [hd, qOfDen, hqodd]⟩
  · have hc : Nat.Coprime j (2 * q) := hj.coprime_two_right.mul_right hcop
    have hd : ((j : ℚ) / (2 * q)).den = 2 * q := by
      have := A_den_coprime j (2 * q) (by omega) hc
      simpa using this
    refine ⟨Or.inr hd, ?_⟩
    simp [hd, qOfDen, Nat.not_odd_iff.mpr (by omega : (2 * q) % 2 = 0)]
end GoldbachBoundaries.Paper2.M2
