import PrimePairNB.HInf.SqFarTail

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2
namespace GoldbachBoundaries.HInf.Fill

/-- The symmetrized main-pair bracket, in `v = 1 + u`. -/
def betaSq (u : ℂ) : ℂ := betaB (1 / 2) (u / 2)

lemma betaSq_ne_zero {u : ℂ} (hu : u.im ≠ 0) : betaSq u ≠ 0 := by
  have h (w : ℂ) (hw : w.im ≠ 0) : Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    apply hw
    simp [hn]
  apply div_ne_zero
  · exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
      (h (u / 2) (by simpa using div_ne_zero hu (by norm_num : (2 : ℝ) ≠ 0)))
  · exact h (1 / 2 + u / 2) (by simpa using div_ne_zero hu (by norm_num : (2 : ℝ) ≠ 0))

lemma betaSq_lower (y ε : ℝ) (hε : 0 < ε) (hεy : ε < y) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ closedBall ((y : ℂ) * I) ε, κ ≤ ‖betaSq u‖ := by
  have him (u : ℂ) (hu : u ∈ closedBall ((y : ℂ) * I) ε) : u.im ≠ 0 := by
    have hn : ‖u - (y : ℂ) * I‖ ≤ ε := by simpa [mem_closedBall, dist_eq_norm] using hu
    have hh := (Complex.abs_im_le_norm (u - (y : ℂ) * I)).trans hn
    have hh' : |u.im - y| ≤ ε := by simpa using hh
    have := (abs_le.mp hh').1
    linarith
  have hcont : ContinuousOn (fun u : ℂ => ‖betaSq u‖) (closedBall ((y : ℂ) * I) ε) := by
    intro u hu
    have hi := him u hu
    have hG (w : ℂ) (hw : w.im ≠ 0) : ContinuousAt Gamma w := by
      apply Complex.continuousAt_Gamma
      intro n hn
      apply hw
      simp [hn]
    have h1 : ContinuousAt (fun z : ℂ => Gamma (z / 2)) u :=
      ContinuousAt.comp (g := Gamma) (f := fun z : ℂ => z / 2)
        (hG (u / 2) (by simpa using div_ne_zero hi (by norm_num : (2 : ℝ) ≠ 0))) (by fun_prop)
    have h2 : ContinuousAt (fun z : ℂ => (Gamma (1 / 2 + z / 2))⁻¹) u :=
      Complex.differentiable_one_div_Gamma.continuous.continuousAt.comp (by fun_prop)
    have hh : ContinuousAt betaSq u := by
      change ContinuousAt (fun z : ℂ => Gamma (1 / 2) * Gamma (z / 2) / Gamma (1 / 2 + z / 2)) u
      simp only [div_eq_mul_inv]
      exact (continuousAt_const.mul h1).mul h2
    exact hh.norm.continuousWithinAt
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall ((y : ℂ) * I) ε).exists_isMinOn
    (nonempty_closedBall.mpr hε.le) hcont
  exact ⟨_, norm_pos_iff.mpr (betaSq_ne_zero (him u hu)), hmin⟩

lemma pairSumSq_eq_terms (x : ℂ) : pairSumSq x = ∑' p : pinchPairs x, pairTermSq p.1 := by
  apply tsum_congr
  intro p
  have hk := (congrArg (kSq p.1.1) p.2.2.2.symm).trans (kSq_at_sum p.1.1 p.1.2)
  rw [hk]
  rfl

lemma pairTermSq_one_left (u : ℂ) : pairTermSq (1, u) = Rcoef u * betaSq u / 2 := by
  simp only [pairTermSq, betaSq, Rcoef_one', one_mul]
  ring

lemma pairTermSq_one_right (u : ℂ) : pairTermSq (u, 1) = Rcoef u * betaSq u / 2 := by
  simp only [pairTermSq, betaSq, betaB, Rcoef_one', mul_one]
  rw [add_comm (u / 2) (1 / 2), mul_comm (Gamma (u / 2)) (Gamma (1 / 2))]
  ring

theorem pairSumSq_ne_zero_of_not_nearBad (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H → ∀ u ∈ PoleSetQ, u ≠ 1 → 0 < u.re → u.re ≤ 1 → |u.im| ≤ Y →
      u ∉ M2.NearBad H Y →
      Real.exp (-H) < ‖Rcoef u * betaSq u‖ → pairSumSq (1 + u) ≠ 0 := by
  classical
  obtain ⟨H₀, -, hfar⟩ := far_tail_Sq hZ1 hZ2 hZ6 hB hY
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
  have hdec : ∀ p : ℂ × ℂ, S.indicator pairTermSq p =
      ((if p = (1, u) then pairTermSq (1, u) else 0) + (if p = (u, 1) then pairTermSq (u, 1) else 0)) +
        Bset.indicator pairTermSq p := by
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
  have hBsum : Summable (Bset.indicator pairTermSq) := by
    rw [← summable_subtype_iff_indicator]
    exact Summable.of_norm hsumm
  have hs1 : Summable fun p : ℂ × ℂ => if p = (1, u) then pairTermSq (1, u) else 0 :=
    summable_of_ne_finset_zero (s := {(1, u)}) (by intro p hp; simp at hp; simp [hp])
  have hs2 : Summable fun p : ℂ × ℂ => if p = (u, 1) then pairTermSq (u, 1) else 0 :=
    summable_of_ne_finset_zero (s := {(u, 1)}) (by intro p hp; simp at hp; simp [hp])
  have hval : pairSumSq (1 + u) = Rcoef u * betaSq u + ∑' p : Bset, pairTermSq p := by
    have e1 : pairSumSq (1 + u) = ∑' p : S, pairTermSq p := pairSumSq_eq_terms (1 + u)
    rw [e1, tsum_subtype S pairTermSq, funext hdec, (hs1.add hs2).tsum_add hBsum, hs1.tsum_add hs2,
      tsum_ite_eq, tsum_ite_eq, ← tsum_subtype Bset pairTermSq, pairTermSq_one_left,
      pairTermSq_one_right]
    ring
  have hnorm : ‖∑' p : Bset, pairTermSq p‖ ≤ Real.exp (-H) :=
    (norm_tsum_le_tsum_norm hsumm).trans htail
  intro h0
  rw [hval] at h0
  have : Rcoef u * betaSq u = -∑' p : Bset, pairTermSq p := eq_neg_of_add_eq_zero_left h0
  rw [this, norm_neg] at hexp
  linarith

lemma pairSumSq_conj (hZ1 : Z1) (s : ℂ) : pairSumSq (conj s) = conj (pairSumSq s) := by
  rw [pairSumSq_eq_terms, pairSumSq_eq_terms, ← (M2.FillF.pinchPairsConj s).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun p => ?_
  have ha := Rcoef_real_conj hZ1 p.2.1
  have hb := Rcoef_real_conj hZ1 p.2.2.1
  have hra : conj (Rcoef p.1.1) = Rcoef p.1.1 := Complex.conj_eq_iff_im.mpr ha.1
  have hrb : conj (Rcoef p.1.2) = Rcoef p.1.2 := Complex.conj_eq_iff_im.mpr hb.1
  change pairTermSq (conj p.1.1, conj p.1.2) = _
  simp only [pairTermSq, betaB, ha.2, hb.2, map_mul, map_div₀, map_add,
    ← Complex.Gamma_conj, map_ofNat, hra, hrb]

/-- Infinitely many good pinches in every boundary window, retaining single representations. -/
theorem prop71_Sq (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    (arithPoints (fun s => pairSumSq s ≠ 0) y ε).Infinite := by
  apply prop71_arith_of_core (fun s => pairSumSq s ≠ 0) ?_ ?_ y ε hε
  · intro s hs
    rw [pairSumSq_conj hZ1]
    exact (map_ne_zero _).mpr hs
  · intro y ε hy hε hεy hε1
    apply sqMix_arith_core hZ1 hZ2 hZ4 hZ5 hB betaSq betaSq_lower
      (fun s => pairSumSq s ≠ 0) ?_ hy hε hεy hε1
    intro Y hY
    exact pairSumSq_ne_zero_of_not_nearBad hZ1 hZ2 hZ6 hB hY

end GoldbachBoundaries.HInf.Fill
