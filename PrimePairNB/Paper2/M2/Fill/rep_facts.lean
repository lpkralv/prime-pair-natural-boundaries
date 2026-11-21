import PrimePairNB.Paper2.M2.QCount

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The representation itself** (unconditional). From `ρ'/k = ρ/q`: `ρ' = kρ/q`, `Re ρ' = k/(2q)`,
`Im ρ' = kγ/q`. `Re ρ' < 1` (definition of `NontrivialZeros`) gives `k < 2q`; `1 ≤ k` is part of `IsRep`. If `q ∣ k`
then `k = q` (the only multiple of `q` in `[1, 2q)`), so `ρ' = ρ`, the excluded pair; hence `¬ q ∣ k`, which for `q`
prime is `Nat.Coprime k q` (`Nat.Coprime.symm`, `(Nat.coprime_primes _ _).mpr` or `Nat.Prime.coprime_iff_not_dvd`),
and `k ≠ q`. -/
theorem rep_facts {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : ρ.re = 1 / 2) {q : ℕ} (hq : q.Prime)
    {ρ' : ℂ} {k : ℕ} (hrep : IsRep (ρ / (q : ℂ)) ρ' k) (hne : (ρ', k) ≠ (ρ, q)) :
    Nat.Coprime k q ∧ 1 ≤ k ∧ k < 2 * q ∧ k ≠ q ∧ ρ'.re = (k : ℝ) / (2 * q) ∧
      ρ'.im = k * ρ.im / q := by
  have hk1 := hrep.2.1
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : k ≠ 0)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have heq : ρ' = (k : ℂ) * (ρ / (q : ℂ)) := by
    rw [← hrep.2.2.2, mul_div_cancel₀ _ hk0]
  have hre' : ρ'.re = (k : ℝ) / (2 * q) := by
    rw [heq]
    simp [div_natCast_re, hre]
    ring
  have him' : ρ'.im = k * ρ.im / q := by
    rw [heq]
    simp [div_natCast_im]
    ring
  have hk2 : k < 2 * q := by
    have h := hrep.1.2.2
    rw [hre', div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)] at h
    exact_mod_cast (by linarith : (k : ℝ) < 2 * q)
  have hkq : k ≠ q := by
    intro h
    apply hne
    simp only [Prod.mk.injEq]
    refine ⟨?_, h⟩
    rw [heq, h, mul_div_cancel₀ _ hq0]
  have hnd : ¬ q ∣ k := by
    rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      by_contra h
      have : m = 0 := by omega
      simp [this] at hm
      omega
    have hm2 : m < 2 := by nlinarith [hq.pos]
    have : m = 1 := by omega
    apply hkq
    simpa [this] using hm
  exact ⟨(hq.coprime_iff_not_dvd.mpr hnd).symm, hrep.2.1, hk2, hkq, hre', him'⟩
end GoldbachBoundaries.Paper2.M2
