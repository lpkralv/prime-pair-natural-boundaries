import PrimePairNB.ThmA.G14_Geometry
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- Facts about a slit disc `Δ(α, r) ∖ cut_α` with `r ≤ Re α - 1`.

Sketch. `|v| ≥ 1`, so inside `ball α r` the cut is the whole radius `{α - tv : 0 ≤ t < r/|v|}`,
i.e. `s ∈ cut_α ↔ (s-α)/v ∈ (-∞, 0]`, i.e. `(s-α)/v ∉ slitPlane`. Open: preimage of `slitPlane`
under a continuous map, intersected with the ball. Connected: star-shaped about
`α + (r/2)·v/|v|` (the slit is the opposite radius). -/
theorem slitDisc_facts (κ : ℝ) {α : ℂ} {r : ℝ} (hr : 0 < r) (hrα : r ≤ α.re - 1) :
    IsOpen (slitDisc (slantDir κ) α r) ∧ IsPreconnected (slitDisc (slantDir κ) α r) ∧
    ∀ s ∈ ball α r, (s ∉ cut (slantDir κ) α ↔ (s - α) / slantDir κ ∈ slitPlane) := by
  have hv := slantDir_ne_zero κ
  let q : ℂ → ℂ := fun s => (s - α) / slantDir κ
  have hq : Continuous q := by fun_prop
  have hequiv : ∀ s ∈ ball α r, (s ∉ cut (slantDir κ) α ↔ q s ∈ slitPlane) := by
    intro s hs
    have hsH : 1 < s.re := ball_subset_HH hrα hs
    constructor
    · intro hcut
      by_contra hslit
      have hnot : ¬ (0 < (q s).re ∨ (q s).im ≠ 0) := by
        simpa only [Complex.mem_slitPlane_iff] using hslit
      have hre : (q s).re ≤ 0 := le_of_not_gt (fun h => hnot (Or.inl h))
      have him : (q s).im = 0 := not_not.mp (fun h => hnot (Or.inr h))
      have hreal : q s = ((q s).re : ℂ) := Complex.ext (by simp) (by simp [him])
      have he : s = α - ((-(q s).re : ℝ) : ℂ) * slantDir κ := by
        have hid : q s * slantDir κ = s - α := div_mul_cancel₀ _ hv
        rw [hreal] at hid
        push_cast
        linear_combination -hid
      apply hcut
      refine ⟨-(q s).re, neg_nonneg.mpr hre, ?_, he⟩
      have heR := congrArg Complex.re he
      simp [slantDir] at heR
      linarith
    · intro hslit hcut
      obtain ⟨t, ht, _, he⟩ := hcut
      have heq : q s = -(t : ℂ) := by
        dsimp [q]
        rw [he]
        field_simp
        ring
      rw [heq, Complex.mem_slitPlane_iff] at hslit
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, neg_zero, ne_self_iff_false, or_false, neg_pos] at hslit
      exact not_lt_of_ge ht hslit
  have hset : slitDisc (slantDir κ) α r = ball α r ∩ q ⁻¹' slitPlane := by
    ext s
    exact and_congr_right (hequiv s)
  refine ⟨?_, ?_, hequiv⟩
  · rw [hset]
    exact isOpen_ball.inter (isOpen_slitPlane.preimage hq)
  · have hnv : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hv
    let c : ℝ := r / (2 * ‖slantDir κ‖)
    have hc : 0 < c := by dsimp [c]; positivity
    let p : ℂ := α + (c : ℂ) * slantDir κ
    have hqp : q p = (c : ℂ) := by simp [q, p, hv]
    have hp : p ∈ ball α r := by
      rw [mem_ball, dist_eq_norm]
      simp only [p, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc]
      dsimp [c]
      field_simp
      linarith
    have hstar : StarConvex ℝ p (q ⁻¹' slitPlane) := by
      intro y hy a b ha hb hab
      have h := (Complex.starConvex_ofReal_slitPlane hc) hy ha hb hab
      change q (a • p + b • y) ∈ slitPlane
      convert h using 1
      have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      simp only [Complex.real_smul]
      rw [← hqp]
      dsimp [q]
      field_simp
      linear_combination α * habC
    rw [hset]
    exact ((convex_ball α r).starConvex hp).inter hstar
      |>.isPathConnected ⟨hp, by change q p ∈ slitPlane; rw [hqp]; exact ofReal_mem_slitPlane.mpr hc⟩
      |>.isConnected.isPreconnected

end GoldbachBoundaries.ThmA
