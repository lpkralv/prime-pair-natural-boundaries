import PrimePairNB.ThmA.G14_Geometry
import PrimePairNB.ThmA.Fill.GeometryCommon

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- Facts about a disc centred on a cut.

Sketch. `s ↦ Im((s-α)/v)` is real-linear, so `V^±` are intersections of a ball with open
half-planes: open and convex. A point `s ∈ V` with `Im((s-α)/v) = 0` is `α - tv`, `t ∈ ℝ`: `t < 0`
is impossible (the segment from `s₀ = α - t₀v`, `t₀ > 0`, to `s` lies in the convex ball and passes
through `α ∉ V`), `t ≥ Re α - 1` is impossible (`Re s ≤ 1`, but `V ⊆ ℍ`), so `s ∈ cut_α`. Points of
`V^±` are off `cut_α` (cut points have `(s-α)/v ∈ (-∞,0]`) and off the other cuts (`IsCutDisc`),
and in `ℍ`, hence in `Ω_ℍ`. -/
theorem cutDisc_facts {κ : ℝ} {α s₀ : ℂ} (hs₀ : s₀ ∈ cut (slantDir κ) α) {r : ℝ}
    (hD : IsCutDisc κ α s₀ r) :
    (∀ s ∈ ball s₀ r, s ∉ cut (slantDir κ) α → s ∈ upperPart κ α s₀ r ∨ s ∈ lowerPart κ α s₀ r) ∧
    upperPart κ α s₀ r ⊆ Omega κ ∧ lowerPart κ α s₀ r ⊆ Omega κ ∧
    IsOpen (upperPart κ α s₀ r) ∧ IsOpen (lowerPart κ α s₀ r) ∧
    Convex ℝ (upperPart κ α s₀ r) ∧ Convex ℝ (lowerPart κ α s₀ r) := by
  have hv := slantDir_ne_zero κ
  let q : ℂ → ℂ := fun s => (s - α) / slantDir κ
  have hq : Continuous q := by fun_prop
  have hsplit : ∀ s ∈ ball s₀ r, s ∉ cut (slantDir κ) α → (q s).im ≠ 0 := by
    intro s hs hnot him
    have hu : 0 < (q s).re := lt_of_not_ge (fun hu =>
      hnot ((geometry_mem_cut_iff κ (hD.1 hs)).mpr ⟨hu, him⟩))
    have hreal : q s = ((q s).re : ℂ) := Complex.ext (by simp) (by simp [him])
    have he : s = α + ((q s).re : ℂ) * slantDir κ := by
      have hid : q s * slantDir κ = s - α := div_mul_cancel₀ _ hv
      rw [hreal] at hid
      linear_combination -hid
    obtain ⟨t, ht, _, he₀⟩ := hs₀
    have hd₀ : dist α s₀ = t * ‖slantDir κ‖ := by
      rw [he₀, dist_eq_norm]
      have : α - (α - (t : ℂ) * slantDir κ) = (t : ℂ) * slantDir κ := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hds : dist s s₀ = ((q s).re + t) * ‖slantDir κ‖ := by
      rw [he₀, dist_eq_norm]
      have : s - (α - (t : ℂ) * slantDir κ) =
          (((q s).re + t : ℝ) : ℂ) * slantDir κ := by
        push_cast
        linear_combination he
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    have hd : dist α s₀ ≤ dist s s₀ := by
      rw [hd₀, hds]
      nlinarith [norm_nonneg (slantDir κ)]
    exact hD.2.1 (mem_ball.mpr (lt_of_le_of_lt hd (mem_ball.mp hs)))
  have hOmega : ∀ s ∈ ball s₀ r, (q s).im ≠ 0 → s ∈ Omega κ := by
    intro s hs him
    refine ⟨hD.1 hs, ?_⟩
    intro hcut
    obtain ⟨α', hα', hsα'⟩ := mem_iUnion₂.mp hcut
    by_cases he : α' = α
    · subst α'
      exact him ((geometry_mem_cut_iff κ (hD.1 hs)).mp hsα').2
    · exact Set.disjoint_left.mp (hD.2.2 α' hα' he) hs hsα'
  have hcplus : Convex ℝ {s : ℂ | 0 < (q s).im} := by
    simpa [q, div_eq_mul_inv, sub_eq_add_neg, add_comm] using
      (((convex_halfSpace_im_gt 0).linear_preimage
        (LinearMap.mulRight ℝ (slantDir κ)⁻¹)).translate_preimage_right (-α))
  have hcminus : Convex ℝ {s : ℂ | (q s).im < 0} := by
    simpa [q, div_eq_mul_inv, sub_eq_add_neg, add_comm] using
      (((convex_halfSpace_im_lt 0).linear_preimage
        (LinearMap.mulRight ℝ (slantDir κ)⁻¹)).translate_preimage_right (-α))
  refine ⟨?_, ?_, ?_, ?_, ?_, (convex_ball _ _).inter hcplus,
    (convex_ball _ _).inter hcminus⟩
  · intro s hs hnot
    rcases lt_or_gt_of_ne (hsplit s hs hnot) with h | h
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨hs, h⟩
  · intro s hs
    exact hOmega s hs.1 (ne_of_gt hs.2)
  · intro s hs
    exact hOmega s hs.1 (ne_of_lt hs.2)
  · exact isOpen_ball.inter (isOpen_lt continuous_const (Complex.continuous_im.comp hq))
  · exact isOpen_ball.inter (isOpen_lt (Complex.continuous_im.comp hq) continuous_const)

end GoldbachBoundaries.ThmA
