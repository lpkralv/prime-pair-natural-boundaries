import PrimePairNB.Paper2.M2.Rigidity
import PrimePairNB.Paper2.M2.Fill.ncard_zeros_le_Nzero
import PrimePairNB.Paper2.M2.Fill.Nzero_le_mul_log

/-! `ncard_notGood_le` of `Paper2/M2/Single.lean`.

For each bad pair `p = (ρ, q)` choose a representation `(ρ', k) ≠ (ρ, q)` of `ρ/q` and put `Φ p = ζ*(ρ', k, q)`.
`lem_rigidity_proof` puts `Φ p` among the zeros with `0 < Im ≤ 2X`; `lem_rigidity_converse_proof` bounds each fibre
of `Φ` by `2` (the fibre lies in `rigPairs z`). So `#bad ≤ 2 N(2X) ≤ 4X log(2X)`. If the bad set is infinite its
`ncard` is `0` and the bound is trivial. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `p` has a representation other than itself. -/
def notGoodHasOtherRep (p : ℂ × ℕ) : Prop :=
  ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p

/-- The chosen zero `ζ*` of a pair with another representation (junk `0` otherwise). -/
def notGoodZeta (p : ℂ × ℕ) : ℂ := by
  classical
  exact if h : notGoodHasOtherRep p then zetaStar (Classical.choose h) (Classical.choose (Classical.choose_spec h)) p.2
    else 0

lemma notGoodZeta_spec {p : ℂ × ℕ} (h : notGoodHasOtherRep p) :
    ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ notGoodZeta p = zetaStar ρ' k p.2 := by
  classical
  refine ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).1,
    (Classical.choose_spec (Classical.choose_spec h)).2, ?_⟩
  unfold notGoodZeta
  simp only [h, dite_true]

lemma notGood_hasOtherRep_of_not_isSingleRep {p : ℂ × ℕ} (h : ¬ IsSingleRep p.1 p.2) : notGoodHasOtherRep p := by
  unfold IsSingleRep at h
  push Not at h
  obtain ⟨ρ', k, hrep, hne⟩ := h
  refine ⟨ρ', k, hrep, fun heq => ?_⟩
  rw [Prod.ext_iff] at heq
  exact hne heq.1 heq.2

/-- **At most `4X log(2X)` pairs are not good** ((Z1), (Z2)). For each `p = (ρ, q) ∈ 𝓟(X)` that is not good choose
a representation `(ρ', k) ≠ (ρ, q)` of `ρ/q` (`IsSingleRep` fails) and put `Φ(p) = zetaStar ρ' k q`. By
`lem_rigidity_proof`, `Φ(p)` is a zero with `0 < Im Φ(p) < 2γ ≤ 2X`, and `Re Φ(p)` is a rational `r`; by
`lem_rigidity_converse_proof` (at `z = Φ(p)`, that `r`) each fibre `Φ⁻¹(z)` lies in a set of at most `2` pairs. So the
number of bad pairs is at most `2 · #{zeros : 0 < Im ≤ 2X} ≤ 2N(2X)` (`ncard_zeros_le_Nzero`)
`≤ 4X log(2X)` (`Nzero_le_mul_log` at `2X`). Counting with fibres: `Finset.card_le_mul_card_image` (fibres of size
`≤ 2`). The set is finite in any case (it injects, up to fibres of size `2`, into a finite set); if one prefers, note
that a junk `ncard = 0` also satisfies the bound. -/
theorem ncard_notGood_le (hZ1 : Z1) (hZ2 : Z2) (A₀ y ε : ℝ) :
    ∀ᶠ X in atTop, (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ≤
      4 * X * Real.log (2 * X) := by
  classical
  have h2X : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  filter_upwards [h2X.eventually (Nzero_le_mul_log hZ2), Filter.eventually_ge_atTop (1 : ℝ)]
    with X hN hX1
  set B := {p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2} with hBdef
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  by_cases hB : B.Finite
  swap
  · rw [Set.Infinite.ncard hB]
    push_cast
    positivity
  set Z := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ 2 * X} with hZdef
  obtain ⟨hZfin, hZN⟩ := ncard_zeros_le_Nzero (2 * X)
  -- facts about a bad pair
  have hfacts : ∀ p ∈ B, ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧
      notGoodZeta p = zetaStar ρ' k p.2 ∧ p ∈ rigPairs (notGoodZeta p) ∧ notGoodZeta p ∈ Z ∧
      ∃ r : ℚ, (r : ℝ) = (notGoodZeta p).re := by
    intro p hp
    obtain ⟨ρ', k, hrep, hne, hΦ⟩ := notGoodZeta_spec (notGood_hasOtherRep_of_not_isSingleRep hp.2)
    obtain ⟨hρ, hre, hlo, hhi, hq, -⟩ := hp.1
    have him : 0 < p.1.im := lt_of_le_of_lt (by positivity) hlo
    obtain ⟨-, -, -, -, -, -, hz, -, hz2, hz3, r, hr, -⟩ :=
      lem_rigidity_proof hZ1 hρ hre him hq ρ' k hrep (by simpa using hne)
    refine ⟨ρ', k, hrep, hne, hΦ, ⟨hρ, hre, him, hq, ρ', k, hrep, hne, hΦ.symm⟩, ?_, r, ?_⟩
    · rw [hΦ]; exact ⟨hz, hz2, by linarith⟩
    · rw [hΦ]; exact hr
  set s := hB.toFinset with hsdef
  have hfib : ∀ a ∈ s.image notGoodZeta, (s.filter fun x => notGoodZeta x = a).card ≤ 2 := by
    intro a ha
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp ha
    rw [Set.Finite.mem_toFinset] at hp0
    obtain ⟨-, -, -, -, -, -, -, r, hr⟩ := hfacts p0 hp0
    obtain ⟨-, hfin, hcard⟩ := lem_rigidity_converse_proof hZ1 (notGoodZeta p0) r hr
    have hsub : (↑(s.filter fun x => notGoodZeta x = notGoodZeta p0) : Set (ℂ × ℕ)) ⊆ rigPairs (notGoodZeta p0) := by
      intro x hx
      rw [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      obtain ⟨hxs, hxe⟩ := hx
      rw [Set.Finite.mem_toFinset] at hxs
      obtain ⟨-, -, -, -, -, hmem, -⟩ := hfacts x hxs
      rw [hxe] at hmem
      exact hmem
    rw [← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hsub hfin).trans hcard
  have hcard := Finset.card_le_mul_card_image s 2 hfib
  have himg : s.image notGoodZeta ⊆ hZfin.toFinset := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    rw [Set.Finite.mem_toFinset] at hp ⊢
    obtain ⟨-, -, -, -, -, -, hZm, -⟩ := hfacts p hp
    exact hZm
  have himgc : (s.image notGoodZeta).card ≤ Z.ncard := by
    rw [Set.ncard_eq_toFinset_card Z hZfin]
    exact Finset.card_le_card himg
  have hBc : B.ncard = s.card := Set.ncard_eq_toFinset_card B hB
  have hfinal : (B.ncard : ℝ) ≤ 2 * (Z.ncard : ℝ) := by
    rw [hBc]
    have : s.card ≤ 2 * Z.ncard := hcard.trans (Nat.mul_le_mul_left 2 himgc)
    exact_mod_cast this
  calc (B.ncard : ℝ) ≤ 2 * (Z.ncard : ℝ) := hfinal
    _ ≤ 2 * Nzero (2 * X) := by linarith
    _ ≤ 2 * ((2 * X) * Real.log (2 * X)) := by linarith
    _ = 4 * X * Real.log (2 * X) := by ring

end GoldbachBoundaries.Paper2.M2
