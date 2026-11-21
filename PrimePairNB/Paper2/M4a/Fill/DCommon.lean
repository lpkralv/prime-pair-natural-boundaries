import PrimePairNB.Paper2.M4a.Defs
import PrimePairNB.SigmaFinite
import PrimePairNB.Density
import PrimePairNB.Paper2.M4a.Fill.segment_subset_Str
import PrimePairNB.Paper2.M4a.Fill.BCommon
import PrimePairNB.Paper2.M4a.Fill.hasDerivAt_Jseg_of_H2b

/-!
# Shared helpers for the kernel bounds

Helpers for the bounds on the Mellin–Barnes kernel.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillD

/-- `(1 + u)^a ≤ (1 + u)^b` for `a ≤ b`, `u ≥ 0`. -/
lemma one_add_rpow_le_of_le {u a b : ℝ} (hu : 0 ≤ u) (hab : a ≤ b) : (1 + u) ^ a ≤ (1 + u) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) hab

/-- Polynomial against `e^{-πu}`: `(1 + u)^E e^{-πu} ≤ K/(1 + u)²` for `u ≥ 0`. -/
lemma exists_rpow_mul_exp_le (E : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ E * Real.exp (-(Real.pi * u)) ≤ K / (1 + u) ^ 2 := by
  set n : ℕ := ⌈max E 0⌉₊ + 2 with hn
  refine ⟨n.factorial * Real.exp 1, by positivity, fun u hu => ?_⟩
  have hpos : 0 < 1 + u := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hE : E + 2 ≤ (n : ℝ) := by
    have := Nat.le_ceil (max E 0)
    have : E ≤ max E 0 := le_max_left _ _
    push_cast [hn]; linarith
  have h1 : (1 + u) ^ E * (1 + u) ^ 2 = (1 + u) ^ (E + 2) := by
    rw [Real.rpow_add hpos]; norm_cast
  have h2 : (1 + u) ^ (E + 2) ≤ (1 + u) ^ n := by
    rw [← Real.rpow_natCast]; exact one_add_rpow_le_of_le hu hE
  have h3 : (1 + u) ^ n ≤ n.factorial * Real.exp (1 + u) := by
    have := Real.pow_div_factorial_le_exp (1 + u) hpos.le n
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h4 : Real.exp (1 + u) * Real.exp (-(Real.pi * u)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc (1 + u) ^ E * Real.exp (-(Real.pi * u)) * (1 + u) ^ 2
      = (1 + u) ^ (E + 2) * Real.exp (-(Real.pi * u)) := by rw [← h1]; ring
    _ ≤ n.factorial * Real.exp (1 + u) * Real.exp (-(Real.pi * u)) := by
        apply mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le
    _ = n.factorial * (Real.exp (1 + u) * Real.exp (-(Real.pi * u))) := by ring
    _ ≤ n.factorial * Real.exp 1 := by gcongr

/-! ### The integral bound for the kernel -/

/-! ### (K2) for `k_r` -/

end FillD

end GoldbachBoundaries.Paper2.M4a
