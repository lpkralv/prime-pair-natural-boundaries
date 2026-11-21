import PrimePairNB.Paper2.M2.Far

/-! `pairSum_ne_zero_of_not_nearBad` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillF

/-- The summand of the pair sum, as a function on `ℂ × ℂ`. -/
def pairTerm (p : ℂ × ℂ) : ℂ := Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2

/-- The two main terms: `R_1 R_u B(1, u) = R_u B(u, 1) R_1 = R_u / u` for `Re u > 0`. -/
lemma pairTerm_one_left {u : ℂ} (hu : 0 < u.re) : pairTerm (1, u) = Rcoef u / u := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hG : Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu
  simp only [pairTerm, betaB, Rcoef_one', Complex.Gamma_one, one_mul]
  rw [add_comm, Complex.Gamma_add_one u hu0]
  field_simp

lemma pairTerm_one_right {u : ℂ} (hu : 0 < u.re) : pairTerm (u, 1) = Rcoef u / u := by
  rw [← pairTerm_one_left hu]
  simp only [pairTerm, betaB, add_comm u 1]
  ring

end FillF

open FillF in
/-- **A main term that wins** (Z1, Z2, Z6, `B < 1`). `H₀` from `lem_far_proof` at `Y`. Off `NearBad H Y`, the pairs
of `pinchPairs (1 + u)` are `(1, u)`, `(u, 1)` and far pairs (`|Im a| > H`), so
`pairSum (1 + u) = 2R_u/u + Σ_far` and `|Σ_far| ≤ e^{-H} < |2R_u/u|`. -/
theorem pairSum_ne_zero_of_not_nearBad (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ}
    (hY : 0 < Y) :
    ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H → ∀ u ∈ PoleSetQ, u ≠ 1 → 0 < u.re → u.re ≤ 1 → |u.im| ≤ Y →
      u ∉ NearBad H Y → Real.exp (-H) < ‖2 * Rcoef u / u‖ → pairSum (1 + u) ≠ 0 := by
  classical
  obtain ⟨-, H₀, -, hfar⟩ := lem_far_proof hZ1 hZ2 hZ6 hB hY
  refine ⟨H₀, fun H hH u hu hu1 hre hre1 hYu hnb hexp => ?_⟩
  obtain ⟨hsumm, htail⟩ := hfar H hH u hre hre1 hYu
  set S := pinchPairs (1 + u) with hS
  set Bset : Set (ℂ × ℂ) := {p | p ∈ pinchPairs (1 + u) ∧ p ≠ (1, u) ∧ p ≠ (u, 1) ∧ H < |p.1.im|}
    with hBset
  have h1u : ((1 : ℂ), u) ≠ (u, 1) := by
    intro h
    exact hu1 (Prod.ext_iff.mp h).1.symm
  have hone : (1 : ℂ) ∈ PoleSetQ := Or.inl (Or.inl rfl)
  have hmem1 : ((1 : ℂ), u) ∈ S := ⟨hone, hu, rfl⟩
  have hmem2 : (u, (1 : ℂ)) ∈ S := ⟨hu, hone, add_comm u 1⟩
  -- every pair of `S` other than the two main ones is far
  have hfarS : ∀ p ∈ S, p ≠ (1, u) → p ≠ (u, 1) → p ∈ Bset := by
    intro p hp h1 h2
    refine ⟨hp, h1, h2, ?_⟩
    by_contra hle
    exact hnb ⟨hre, hre1, hYu, p, hp, h1, h2, le_of_not_gt hle⟩
  -- pointwise decomposition of the indicator
  have hdec : ∀ p : ℂ × ℂ, S.indicator pairTerm p =
      ((if p = (1, u) then pairTerm (1, u) else 0) + (if p = (u, 1) then pairTerm (u, 1) else 0)) +
        Bset.indicator pairTerm p := by
    intro p
    by_cases h1 : p = (1, u)
    · subst h1
      have hnB : ((1 : ℂ), u) ∉ Bset := fun h => h.2.1 rfl
      simp [Set.indicator_of_mem hmem1, Set.indicator_of_notMem hnB, h1u]
    by_cases h2 : p = (u, 1)
    · subst h2
      have hnB : (u, (1 : ℂ)) ∉ Bset := fun h => h.2.2.1 rfl
      simp [Set.indicator_of_mem hmem2, Set.indicator_of_notMem hnB, h1u.symm]
    simp only [h1, h2, ite_false, zero_add]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hfarS p hp h1 h2)]
    · have hnB : p ∉ Bset := fun h => hp h.1
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hnB]
  have hBsum : Summable (Bset.indicator pairTerm) := by
    rw [← summable_subtype_iff_indicator]
    exact Summable.of_norm hsumm
  have hs1 : Summable fun p : ℂ × ℂ => if p = (1, u) then pairTerm (1, u) else 0 :=
    summable_of_ne_finset_zero (s := {(1, u)}) (by intro p hp; simp at hp; simp [hp])
  have hs2 : Summable fun p : ℂ × ℂ => if p = (u, 1) then pairTerm (u, 1) else 0 :=
    summable_of_ne_finset_zero (s := {(u, 1)}) (by intro p hp; simp at hp; simp [hp])
  have hval : pairSum (1 + u) = 2 * Rcoef u / u + ∑' p : Bset, pairTerm p := by
    have e1 : pairSum (1 + u) = ∑' p : S, pairTerm p := rfl
    rw [e1, tsum_subtype S pairTerm, funext hdec, (hs1.add hs2).tsum_add hBsum, hs1.tsum_add hs2,
      tsum_ite_eq, tsum_ite_eq, ← tsum_subtype Bset pairTerm, pairTerm_one_left hre,
      pairTerm_one_right hre]
    ring
  have hnorm : ‖∑' p : Bset, pairTerm p‖ ≤ Real.exp (-H) :=
    (norm_tsum_le_tsum_norm hsumm).trans htail
  intro h0
  rw [hval] at h0
  have : 2 * Rcoef u / u = -∑' p : Bset, pairTerm p := eq_neg_of_add_eq_zero_left h0
  rw [this, norm_neg] at hexp
  linarith

end GoldbachBoundaries.Paper2.M2
