import PrimePairNB.Paper2.M2.QCount
import PrimePairNB.Paper2.M2.Fill.den_div_two_mul_prime
import PrimePairNB.Paper2.M2.Fill.rep_facts
import PrimePairNB.Paper2.M2.Fill.rigPairs_mem_pairOf
import PrimePairNB.Paper2.M2.Fill.zetaStar_facts

/-!
# Rigidity of representations on the critical line (Paper, Lemma 3.2)

`ρ = 1/2 + iγ` a zero (`γ > 0`), `q` prime, `u = ρ/q`. A representation `(ρ', k) ≠ (ρ, q)` of `u` has
`ρ' = kρ/q`, so `Re ρ' = k/(2q)`, `Im ρ' = kγ/q`; `Re ρ' < 1` gives `k < 2q`, and `q ∣ k` would force `k = q`,
`ρ' = ρ`. The zero `ζ* = zetaStar ρ' k q` (`ρ'` if `k > q`, `1 - ρ̄'` if `k < q`, a zero by (Z1)) has real part
`j/(2q)` with `q < j < 2q`, `gcd(j, q) = 1`; the reduced denominator of `j/(2q)` is `q` or `2q` and gives `q` back
(`qOfDen`). Given `q`, `ρ' ∈ {ζ*, 1 - ζ̄*}` and `ρ = qρ'/(2q Re ρ')` (`pairOf`), so at most two pairs.

The targets `lem_rigidity_proof`, `lem_rigidity_converse_proof` are at the end of this file (`Single.lean` uses them).
The lemmas `rep_facts`, `zetaStar_facts`, `den_div_two_mul_prime`, `rigPairs_mem_pairOf` are proved in
`Fill/<name>.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Targets -/

/-- `lem_rigidity` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_rigidity_proof (hZ1 : Z1) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {q : ℕ} (hq : q.Prime) :
    ∀ ρ' : ℂ, ∀ k : ℕ, IsRep (ρ / (q : ℂ)) ρ' k → (ρ', k) ≠ (ρ, q) →
      Nat.Coprime k q ∧ 1 ≤ k ∧ k < 2 * q ∧ k ≠ q ∧ ρ'.re = (k : ℝ) / (2 * q) ∧ ρ'.re ≠ 1 / 2 ∧
      zetaStar ρ' k q ∈ NontrivialZeros ∧ 1 / 2 < (zetaStar ρ' k q).re ∧
      0 < (zetaStar ρ' k q).im ∧ (zetaStar ρ' k q).im < 2 * ρ.im ∧
      ∃ r : ℚ, (r : ℝ) = (zetaStar ρ' k q).re ∧ (r.den = q ∨ r.den = 2 * q) := by
  intro ρ' k hrep hne
  obtain ⟨hcop, hk1, hk2, hkq, hre', -⟩ := rep_facts hρ hre hq hrep hne
  obtain ⟨hz, hz1, hz2, hz3, j, hj1, hj2, hjc, hjre⟩ := zetaStar_facts hZ1 hρ hre him hq hrep hne
  refine ⟨hcop, hk1, hk2, hkq, hre', ?_, hz, hz1, hz2, hz3, (j : ℚ) / (2 * q), ?_,
    (den_div_two_mul_prime hq hj1 hj2 hjc).1⟩
  · rw [hre']
    intro h
    apply hkq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have h2 : (k : ℝ) = q := by
      field_simp at h
      linarith
    exact_mod_cast h2
  · rw [hjre]
    push_cast
    ring

/-- `lem_rigidity_converse` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_rigidity_converse_proof (hZ1 : Z1) (z : ℂ) (r : ℚ) (hr : (r : ℝ) = z.re) :
    (∀ p ∈ {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z},
      p.2 = if Odd r.den then r.den else r.den / 2) ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.Finite ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.ncard ≤ 2 := by
  have hq : ∀ p ∈ rigPairs z, p.2 = qOfDen r.den := by
    rintro ⟨ρ, q⟩ ⟨hρ, hre, him, hqp, ρ', k, hrep, hne, hz⟩
    obtain ⟨-, -, -, -, j, hj1, hj2, hjc, hjre⟩ := zetaStar_facts hZ1 hρ hre him hqp hrep hne
    have hrj : r = (j : ℚ) / (2 * q) := by
      have h : (r : ℝ) = (((j : ℚ) / (2 * q) : ℚ) : ℝ) := by
        rw [hr, ← hz, hjre]
        push_cast
        ring
      exact_mod_cast h
    rw [hrj]
    exact (den_div_two_mul_prime hqp hj1 hj2 hjc).2.symm
  have hsub : rigPairs z ⊆ {pairOf (qOfDen r.den) z, pairOf (qOfDen r.den) (1 - conj z)} := by
    intro p hp
    have h2 := hq p hp
    rcases rigPairs_mem_pairOf hp with h | h
    · rw [h2] at h
      exact Or.inl h
    · rw [h2] at h
      exact Or.inr h
  refine ⟨fun p hp => hq p hp, (Set.toFinite _).subset hsub, ?_⟩
  calc (rigPairs z).ncard
      ≤ ({pairOf (qOfDen r.den) z, pairOf (qOfDen r.den) (1 - conj z)} : Set (ℂ × ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({pairOf (qOfDen r.den) (1 - conj z)} : Set (ℂ × ℕ)).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

end GoldbachBoundaries.Paper2.M2
