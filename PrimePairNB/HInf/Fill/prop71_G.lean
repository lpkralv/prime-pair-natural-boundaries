import PrimePairNB.HInf.Defs

/-!
# `prop71_G`

This is `Paper2.M2.prop_Lambda_proof`, statement for statement. The change of `prop71_joint` to carry `IsSingleRep ρ q`
does not touch it: `prop71_G` states `pairSum s₀ ≠ 0` with no representation clause, and `boundary_G` uses only that.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- For `G`: if `B < 1`, every ball about `1 + iy` contains infinitely many points `1 + ρ/q` with `pairSum ≠ 0`. -/
theorem prop71_G (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0}.Infinite :=
  M2.prop_Lambda_proof hZ1 hZ2 hZ4 hZ5 hZ6 hB y ε hε

end GoldbachBoundaries.HInf.Fill
