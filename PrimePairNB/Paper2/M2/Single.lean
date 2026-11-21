import PrimePairNB.Paper2.M2.Rigidity
import PrimePairNB.Paper2.M2.Fill.Nzero_le_mul_log
import PrimePairNB.Paper2.M2.Fill.Rcoef_div_of_isSingleRep
import PrimePairNB.Paper2.M2.Fill.eventually_four_mul_log_le
import PrimePairNB.Paper2.M2.Fill.BCommon
import PrimePairNB.Paper2.M2.Fill.ncard_notGood_le
import PrimePairNB.Paper2.M2.Fill.ncard_zeros_le_Nzero
import PrimePairNB.Paper2.M2.Fill.singlePairs_bounds
import PrimePairNB.Paper2.M2.Fill.singlePairs_finite_ncard_ge
import PrimePairNB.Paper2.M2.Fill.singlePairs_injOn

/-!
# Single-representation points on the critical line (Paper, Theorem 3.3)

The count of `𝓟(X) = singlePairs A₀ y ε X`: at least `A₀X/2` distinct zeros `1/2 + iγ` with `X/M < γ ≤ X`
((Z4) through the witnesses `A₀, t₀`, and (Z2) for `N(X/M) ≤ (X/M) log X`), each with at least `c₁ X/log²X` primes
`q` such that `γ/q ∈ J` ((Z5) on `(x, (1+θ)x)`, `x = γ/(y + ε/2)`, `θ = ε/(y - ε/2)`). The pairs that are not good map
to zeros `ζ*` with `0 < Im ζ* < 2X` with fibres of size at most `2` (`lem_rigidity_proof`,
`lem_rigidity_converse_proof`), so there are at most `2N(2X) ≤ 4X log(2X)` of them ((Z2)).

All asymptotic statements are `∀ᶠ X in atTop`; the target chooses `X₀` from their conjunction
(`Filter.eventually_atTop`). The target `thm_single_proof` is at the end of this file (`Lambda.lean` uses it).
The lemmas `ncard_zeros_le_Nzero`, `Nzero_le_mul_log`, `singlePairs_finite_ncard_ge`, `ncard_notGood_le`,
`Rcoef_div_of_isSingleRep`, `singlePairs_bounds`, `singlePairs_injOn`, `eventually_four_mul_log_le` are proved in
`Fill/<name>.lean`; for the counting lemmas the proofs are the `<name>B` lemmas of `Fill/BCommon.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Targets -/

/-- `thm_single` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_single_proof (hZ1 : Z1) (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 3 ≤ X →
      (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) ∧
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ≤
        4 * X * Real.log (2 * X) ∧
      c₂ / 2 * X ^ 2 / Real.log X ^ 2 ≤
        (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ∧
      (∀ p ∈ singlePairs A₀ y ε X, IsSingleRep p.1 p.2 →
        ‖p.1 / (p.2 : ℂ) - y * I‖ < ε ∧ (p.1 / (p.2 : ℂ)).re = 1 / (2 * p.2) ∧
        Rcoef (p.1 / (p.2 : ℂ)) = (zetaMult p.1 : ℂ) / p.2 ∧ Rcoef (p.1 / (p.2 : ℂ)) ≠ 0 ∧
        ‖2 * Rcoef (p.1 / (p.2 : ℂ)) / (p.1 / (p.2 : ℂ))‖ = 2 * zetaMult p.1 / ‖p.1‖ ∧
        2 / (X + 1) ≤ 2 * zetaMult p.1 / ‖p.1‖) ∧
      InjOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (singlePairs A₀ y ε X) := by
  obtain ⟨c₂, hc₂, hP⟩ := singlePairs_finite_ncard_ge hZ2 hZ5 hA₀ hN0 hy hε hεy
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hP.and ((ncard_notGood_le hZ1 hZ2 A₀ y ε).and
      ((singlePairs_bounds hA₀ hy hε hεy).and (eventually_four_mul_log_le hc₂))))
  refine ⟨c₂, hc₂, X₀, fun X hX _ => ?_⟩
  obtain ⟨⟨hfin, hcard⟩, hbad, hb, h4⟩ := hX₀ X hX
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (singlePairs A₀ y ε X)
    {p : ℂ × ℕ | IsSingleRep p.1 p.2} hfin
  have hsplit' : (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) +
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) =
        ((singlePairs A₀ y ε X).ncard : ℝ) := by
    exact_mod_cast hsplit
  have hhalf : c₂ / 2 * X ^ 2 / Real.log X ^ 2 = (c₂ * X ^ 2 / Real.log X ^ 2) / 2 := by ring
  refine ⟨hfin, hcard, hbad, by linarith, fun p hp hs => ?_, singlePairs_injOn A₀ y ε X⟩
  obtain ⟨h1, h2, h3⟩ := hb p hp
  have hq : p.2.Prime := hp.2.2.2.2.1
  obtain ⟨hR, hn⟩ := Rcoef_div_of_isSingleRep hp.1 hq hs
  refine ⟨h1, h2, hR, ?_, hn, h3⟩
  rw [hR]
  have hm : zetaMult p.1 ≠ 0 := by
    have := one_le_zetaMult hp.1
    omega
  exact div_ne_zero (by exact_mod_cast hm) (by exact_mod_cast hq.ne_zero)

end GoldbachBoundaries.Paper2.M2
