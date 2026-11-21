import PrimePairNB.HInf.Fill.far_tail_S

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M2 GoldbachBoundaries.Paper2.M1
namespace GoldbachBoundaries.HInf.Fill

private def pairTermS (p : ℂ × ℂ) : ℂ := Rcoef p.1 * Rcoef p.2 * KS ((p.1 - p.2 + 3) / 4)

private lemma pairTermS_one_left (u : ℂ) : pairTermS (1, u) = Rcoef u * KS (1 - u / 4) := by
  simp only [pairTermS, Rcoef_one', one_mul]
  congr 2
  ring

private lemma pairTermS_one_right (u : ℂ) : pairTermS (u, 1) = Rcoef u * KS (1 / 2 + u / 4) := by
  simp only [pairTermS, Rcoef_one', mul_one]
  congr 2
  ring

theorem pairSumS_ne_zero_of_not_nearBad (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H → ∀ u ∈ PoleSetQ, u ≠ 1 → 0 < u.re → u.re ≤ 1 → |u.im| ≤ Y →
      u ∉ M2.NearBad H Y →
      Real.exp (-H) < ‖Rcoef u * (KS (1 - u / 4) + KS (1 / 2 + u / 4))‖ → pairSumS (1 + u) ≠ 0 := by
  classical
  obtain ⟨H₀, -, hfar⟩ := far_tail_S hZ1 hZ2 hB hY
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
  have hdec : ∀ p : ℂ × ℂ, S.indicator pairTermS p =
      ((if p = (1, u) then pairTermS (1, u) else 0) + (if p = (u, 1) then pairTermS (u, 1) else 0)) +
        Bset.indicator pairTermS p := by
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
  have hBsum : Summable (Bset.indicator pairTermS) := by
    rw [← summable_subtype_iff_indicator]
    exact Summable.of_norm hsumm
  have hs1 : Summable fun p : ℂ × ℂ => if p = (1, u) then pairTermS (1, u) else 0 :=
    summable_of_ne_finset_zero (s := {(1, u)}) (by intro p hp; simp at hp; simp [hp])
  have hs2 : Summable fun p : ℂ × ℂ => if p = (u, 1) then pairTermS (u, 1) else 0 :=
    summable_of_ne_finset_zero (s := {(u, 1)}) (by intro p hp; simp at hp; simp [hp])
  have hval : pairSumS (1 + u) = Rcoef u * (KS (1 - u / 4) + KS (1 / 2 + u / 4)) + ∑' p : Bset, pairTermS p := by
    have e1 : pairSumS (1 + u) = ∑' p : S, pairTermS p := rfl
    rw [e1, tsum_subtype S pairTermS, funext hdec, (hs1.add hs2).tsum_add hBsum, hs1.tsum_add hs2,
      tsum_ite_eq, tsum_ite_eq, ← tsum_subtype Bset pairTermS, pairTermS_one_left,
      pairTermS_one_right]
    ring
  have hnorm : ‖∑' p : Bset, pairTermS p‖ ≤ Real.exp (-H) :=
    (norm_tsum_le_tsum_norm hsumm).trans htail
  intro h0
  rw [hval] at h0
  have : Rcoef u * (KS (1 - u / 4) + KS (1 / 2 + u / 4)) = -∑' p : Bset, pairTermS p := eq_neg_of_add_eq_zero_left h0
  rw [this, norm_neg] at hexp
  linarith

end GoldbachBoundaries.HInf.Fill
