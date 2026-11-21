import PrimePairNB.HInf.Fill.prop71_S

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

theorem prop71_joint (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      IsSingleRep ρ q ∧ s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0 ∧ pairSumS s₀ ≠ 0}.Infinite := by
  change (arithPoints (fun s => pairSum s ≠ 0 ∧ pairSumS s ≠ 0) y ε).Infinite
  apply prop71_arith_of_core (fun s => pairSum s ≠ 0 ∧ pairSumS s ≠ 0) ?_ ?_ y ε hε
  · intro s hs
    rw [M2.pairSum_conj hZ1, pairSumS_conj hZ1]
    exact ⟨(map_ne_zero _).mpr hs.1, (map_ne_zero _).mpr hs.2⟩
  · intro y ε hy hε hεy hε1
    apply prop71_arith_core hZ1 hZ2 hZ4 hZ5 hB
      (fun s => pairSum s ≠ 0 ∧ pairSumS s ≠ 0) ?_ hy hε hεy hε1
    intro Y hY
    obtain ⟨HG, hG⟩ := M2.pairSum_ne_zero_of_not_nearBad hZ1 hZ2 hZ6 hB hY
    obtain ⟨HS, hS⟩ := pairSumS_ne_zero_of_not_nearBad hZ1 hZ2 hB hY
    refine ⟨max HG HS, ?_⟩
    intro H hH u hu hu1 hre hre1 hYu hnB heG heS
    exact ⟨hG H ((le_max_left _ _).trans hH) u hu hu1 hre hre1 hYu hnB heG,
      hS H ((le_max_right _ _).trans hH) u hu hu1 hre hre1 hYu hnB heS⟩

end GoldbachBoundaries.HInf.Fill
