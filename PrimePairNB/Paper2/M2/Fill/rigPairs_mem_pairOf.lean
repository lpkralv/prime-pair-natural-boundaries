import PrimePairNB.Paper2.M2.QCount
import PrimePairNB.Paper2.M2.Fill.rep_facts

noncomputable section
open Complex ComplexConjugate
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **A pair is recovered from `ζ*` and `q`** (unconditional). For `p = (ρ, q) ∈ rigPairs z` with witness
`(ρ', k)`: `k ≠ q` (`rep_facts`); if `q < k` then `ζ* = ρ' = z`, else `z = 1 - ρ̄'`, i.e. `ρ' = 1 - z̄`. In both cases
`k = 2q Re ρ'` (from `Re ρ' = k/(2q)`) and `ρ = qρ'/k` (from `ρ'/k = ρ/q`), which is `pairOf q ρ'`. -/
theorem rigPairs_mem_pairOf {z : ℂ} {p : ℂ × ℕ} (hp : p ∈ rigPairs z) :
    p = pairOf p.2 z ∨ p = pairOf p.2 (1 - conj z) := by
  rcases p with ⟨ρ, q⟩
  obtain ⟨hρ, hr, hi, hq, ρ', k, hrep, hne, hz⟩ := hp
  obtain ⟨hc, hk1, hk2, hkq, hr', hi'⟩ := rep_facts hρ hr hq hrep hne
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hkr : 2 * q * ρ'.re = (k : ℝ) := by rw [hr']; field_simp
  have heq : (ρ, q) = pairOf q ρ' := by
    unfold pairOf
    congr 1
    rw [hkr]
    push_cast
    have he := hrep.2.2.2
    field_simp at he ⊢
    linear_combination -he
  by_cases h : q < k
  · left
    simp only [zetaStar, if_pos h] at hz
    rw [← hz]
    exact heq
  · right
    have hz' : 1 - conj z = ρ' := by
      rw [← hz]
      simp [zetaStar, h]
    simpa only [Prod.snd, hz'] using heq
end GoldbachBoundaries.Paper2.M2
