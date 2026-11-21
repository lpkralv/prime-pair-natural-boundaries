import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Real parts of `Σ_Q`, without RH: `0 < Re a ≤ 1`, and `Re a ≤ 1/2` unless `a = 1` or `a` is a zero
(for `k ≥ 2`, `1/k ≤ 1/2` and `β/k < 1/2`). -/
theorem poleSetQ_re_bounds {a : ℂ} (ha : a ∈ PoleSetQ) :
    0 < a.re ∧ a.re ≤ 1 ∧ (a ≠ 1 → a ∉ NontrivialZeros → a.re ≤ 1 / 2) := by
  refine ⟨re_pos_of_mem_poleSetQ ha, ?_⟩
  rcases ha with (ha | ⟨k, hk, hs, rfl⟩) | ⟨n, hn, hs, ρ, hρ, rfl⟩
  · subst a
    norm_num
  · rw [re_one_div_natCast]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hb : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkR
    exact ⟨by linarith, fun _ _ => hb⟩
  · rw [Complex.div_natCast_re]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨(div_le_self hρ.2.1.le hnR).trans hρ.2.2.le, ?_⟩
    intro _ hz
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n = 1 := by omega
      simp [this, hρ] at hz
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    calc
      ρ.re / (n : ℝ) ≤ 1 / (n : ℝ) := div_le_div_of_nonneg_right hρ.2.2.le (by positivity)
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2R

end GoldbachBoundaries.Paper2.M1
