import PrimePairNB.HInf.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Arcs made from disjoint smooth tents. No HInf theorem is used. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

private lemma arc_of_smooth {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} {ξ : ℝ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (he : ξ (-r₀) = 0 ∧ ξ r₀ = 0)
    (hb : ∀ h : ℝ, |ξ h| < r₀ / 2) (h0 : 0 < ξ 0) (hy : ξ ε.im < ε.re) :
    IsArc r₀ ε ξ := by
  refine ⟨hξ.continuous.continuousOn, ⟨∅, fun h _ _ =>
    (hξ.differentiable (by norm_num)) h⟩, ?_, he, ?_, h0, hy⟩
  · obtain ⟨L, hL⟩ := hξ.continuous_deriv_one.bounded_above_of_compact_support hc.deriv
    exact ⟨L, fun h _ => by simpa only [Real.norm_eq_abs] using hL h⟩
  · intro h hh
    have hh' : |h| ≤ r₀ := abs_le.mpr hh
    calc ‖(ξ h : ℂ) + (h : ℂ) * I‖ ≤ ‖(ξ h : ℂ)‖ + ‖(h : ℂ) * I‖ := norm_add_le _ _
      _ = |ξ h| + |h| := by simp
      _ < 3 * r₀ / 2 := by linarith [hb h]

/-- `ε` off the cut `(-∞, 0]`, small: an arc exists. 1, "Arcs" (polygon through `η` and `ε - η`, through
`ε/2` if `ε > 0`). -/
theorem exists_arc {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ} (hε : ‖ε‖ < r₀ / 4) (hslit : ε ∈ slitPlane) :
    ∃ ξ : ℝ → ℝ, IsArc r₀ ε ξ := by
  have hre : |ε.re| < r₀ / 4 := (abs_re_le_norm ε).trans_lt hε
  have him : |ε.im| < r₀ / 4 := (abs_im_le_norm ε).trans_lt hε
  by_cases hy : ε.im = 0
  · have hx : 0 < ε.re := by simpa [slitPlane, hy] using hslit
    let b : ContDiffBump (0 : ℝ) :=
      { rIn := r₀ / 4, rOut := r₀ / 2
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    have hb0 : b 0 = 1 := b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
    let ξ : ℝ → ℝ := fun h => (ε.re / 2) * b h
    have hc : HasCompactSupport ξ := b.hasCompactSupport.mul_left
    have hz : b (-r₀) = 0 ∧ b r₀ = 0 := by
      constructor <;> apply b.zero_of_le_dist <;>
        simp only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr₀] <;>
        change r₀ / 2 ≤ r₀ <;> linarith
    refine ⟨ξ, arc_of_smooth hr₀ (contDiff_const.mul b.contDiff) hc ?_ ?_ ?_ ?_⟩
    · simp [ξ, hz.1, hz.2]
    · intro h
      have hbh : 0 ≤ b h := b.nonneg
      have hbh' : b h ≤ 1 := b.le_one
      dsimp [ξ]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [abs_lt.mp hre]
    · simpa only [ξ, hb0, mul_one] using (half_pos hx)
    · simp only [ξ, hy, hb0, mul_one]
      linarith
  · let d : ℝ := |ε.im| / 2
    have hd : 0 < d := by dsimp [d]; exact half_pos (abs_pos.mpr hy)
    let b (a : ℝ) : ContDiffBump a :=
      { rIn := d / 2, rOut := d
        rIn_pos := by positivity
        rIn_lt_rOut := by linarith }
    have hzero (a h : ℝ) (hh : d ≤ |h - a|) : b a h = 0 :=
      (b a).zero_of_le_dist (by simpa only [Real.dist_eq] using hh)
    have hz0 : b ε.im 0 = 0 := hzero _ _ (by simp [d])
    have hzy : b 0 ε.im = 0 := hzero _ _ (by simp [d])
    have hend (a : ℝ) (ha : a = 0 ∨ a = ε.im) : b a (-r₀) = 0 ∧ b a r₀ = 0 := by
      have ha' : |a| < r₀ / 4 := by rcases ha with rfl | rfl <;> simp_all
      constructor <;> apply hzero
      · have := abs_sub_abs_le_abs_sub (-r₀) a
        rw [abs_neg, abs_of_pos hr₀] at this
        dsimp [d]
        linarith
      · have := abs_sub_abs_le_abs_sub r₀ a
        rw [abs_of_pos hr₀] at this
        dsimp [d]
        linarith
    have hbcenter (a : ℝ) : b a a = 1 :=
      (b a).one_of_mem_closedBall (mem_closedBall_self (b a).rIn_pos.le)
    let ξ : ℝ → ℝ := fun h => (r₀ / 8) * b 0 h + (ε.re - r₀ / 8) * b ε.im h
    have hξ : ContDiff ℝ 1 ξ :=
      (contDiff_const.mul (b 0).contDiff).add (contDiff_const.mul (b ε.im).contDiff)
    have hc : HasCompactSupport ξ :=
      ((b 0).hasCompactSupport.mul_left).add ((b ε.im).hasCompactSupport.mul_left)
    refine ⟨ξ, arc_of_smooth hr₀ hξ hc ?_ ?_ ?_ ?_⟩
    · have h1 := hend 0 (Or.inl rfl)
      have h2 := hend ε.im (Or.inr rfl)
      simp [ξ, h1.1, h1.2, h2.1, h2.2]
    · intro h
      have h1 : |b 0 h| ≤ 1 := by rw [abs_of_nonneg (b 0).nonneg]; exact (b 0).le_one
      have h2 : |b ε.im h| ≤ 1 := by rw [abs_of_nonneg (b ε.im).nonneg]; exact (b ε.im).le_one
      have h3 : |ε.re - r₀ / 8| ≤ |ε.re| + r₀ / 8 := by
        simpa only [abs_of_pos (show 0 < r₀ / 8 by positivity)] using abs_sub ε.re (r₀ / 8)
      calc |ξ h| ≤ |(r₀ / 8) * b 0 h| + |(ε.re - r₀ / 8) * b ε.im h| := abs_add_le _ _
        _ ≤ r₀ / 8 + |ε.re - r₀ / 8| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ r₀ / 8 by positivity)]
          nlinarith [abs_nonneg (ε.re - r₀ / 8)]
        _ < r₀ / 2 := by linarith
    · simp only [ξ, hbcenter 0, hz0, mul_one, mul_zero, add_zero]
      positivity
    · simp only [ξ, hzy, hbcenter ε.im, mul_zero, mul_one, zero_add]
      linarith

end GoldbachBoundaries.HInf.Fill

