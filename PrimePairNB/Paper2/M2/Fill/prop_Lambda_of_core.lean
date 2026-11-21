import PrimePairNB.Paper2.M2.Far
import PrimePairNB.Paper2.M2.Fill.pairSum_conj

/-! `prop_Lambda_of_core` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillF

/-- `LambdaSet` is monotone in the radius. -/
lemma lambdaSet_mono_radius {y ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) : LambdaSet y ε₁ ⊆ LambdaSet y ε₂ := by
  rintro s ⟨ρ, hρ, hre, q, hq, rfl, hball, hne⟩
  exact ⟨ρ, hρ, hre, q, hq, rfl, Metric.ball_subset_ball h hball, hne⟩

/-- Conjugation maps `LambdaSet (-y) ε` into `LambdaSet y ε` (Z1, through `pairSum_conj`). -/
lemma conj_mem_lambdaSet (hZ1 : Z1) {y ε : ℝ} {s : ℂ} (hs : s ∈ LambdaSet (-y) ε) :
    conj s ∈ LambdaSet y ε := by
  obtain ⟨ρ, hρ, hre, q, hq, rfl, hball, hne⟩ := hs
  refine ⟨conj ρ, conj_mem_nontrivialZeros hρ, by simpa using hre, q, hq, ?_, ?_, ?_⟩
  · simp [map_div₀]
  · have hc : (1 : ℂ) + (y : ℂ) * I = conj (1 + ((-y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [mem_ball, hc, Complex.dist_conj_conj]
    exact hball
  · rw [pairSum_conj hZ1]
    exact (map_ne_zero _).mpr hne

end FillF

open FillF in
/-- **Reduction to `y > 0`, small `ε`** (Z1; the paper's reductions). -/
theorem prop_Lambda_of_core (hZ1 : Z1)
    (hcore : ∀ y ε : ℝ, 0 < y → 0 < ε → ε < y → ε < 1 → (LambdaSet y ε).Infinite) (y ε : ℝ) (hε : 0 < ε) :
    (LambdaSet y ε).Infinite := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · -- `y < 0`: conjugate from `-y`.
    set ε' := min ε (min (-y / 2) (1 / 2)) with hε'
    have h0 : 0 < ε' := lt_min hε (lt_min (by linarith) (by norm_num))
    have h1 : ε' < -y := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have h2 : ε' < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    have hinf := hcore (-y) ε' (by linarith) h0 h1 h2
    have himg : (conj '' LambdaSet (-y) ε').Infinite :=
      hinf.image (star_injective.injOn)
    refine himg.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s ∈ LambdaSet (-y) ε := lambdaSet_mono_radius (min_le_left _ _) hs
    exact conj_mem_lambdaSet hZ1 hs'
  · -- `y = 0`: points near `1 + iε/2`.
    set ε₃ := min (ε / 4) (1 / 2) with hε₃
    have h0 : 0 < ε₃ := lt_min (by linarith) (by norm_num)
    have h1 : ε₃ < ε / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h2 : ε₃ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine (hcore (ε / 2) ε₃ (by linarith) h0 h1 h2).mono ?_
    rintro s ⟨ρ, hρ, hre, q, hq, rfl, hball, hne⟩
    refine ⟨ρ, hρ, hre, q, hq, rfl, ?_, hne⟩
    refine Metric.ball_subset_ball' ?_ hball
    have hd : dist (1 + ((ε / 2 : ℝ) : ℂ) * I) (1 + ((0 : ℝ) : ℂ) * I) = ε / 2 := by
      rw [Complex.dist_eq]
      simp only [ofReal_zero, zero_mul, add_zero, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    rw [hd]
    linarith [min_le_left (ε / 4) (1 / 2)]
  · -- `y > 0`: shrink the radius.
    set ε' := min ε (min (y / 2) (1 / 2)) with hε'
    have h0 : 0 < ε' := lt_min hε (lt_min (by linarith) (by norm_num))
    have h1 : ε' < y := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have h2 : ε' < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    exact (hcore y ε' hy h0 h1 h2).mono (lambdaSet_mono_radius (min_le_left _ _))

end GoldbachBoundaries.Paper2.M2
