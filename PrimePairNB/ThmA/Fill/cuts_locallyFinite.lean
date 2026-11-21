import PrimePairNB.ThmA.G14_Geometry
import PrimePairNB.ThmA.Fill.GeometryCommon

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- The family of cuts is locally finite in `ℍ`, so `Ω_ℍ` is open (any slope).

Sketch. A cut meeting `ball z ε` with `Re z - ε ≥ 1 + ε` starts at `α` with
`Re α ≥ 1 + ε` (cut points have real part `≤ Re α`) and `|Im α| ≤ |Im z| + ε + |κ|` (cut points
are `α - tv`, `0 ≤ t < Re α - 1 ≤ 1`); finitely many by `catalogue_locallyFinite` (applied on a compact rectangle). Each
`cut v α = (closed ray) ∩ ℍ` is closed in `ℍ`; a locally finite union of relatively closed sets is
relatively closed (`LocallyFinite.isClosed_iUnion` on the subtype, or by hand). -/
theorem cuts_locallyFinite (κ : ℝ) :
    (∀ z ∈ HH, ∃ U ∈ 𝓝 z, {α ∈ catalogue | (U ∩ cut (slantDir κ) α).Nonempty}.Finite) ∧
    IsOpen (Omega κ) := by
  have hlocal : ∀ z ∈ HH, ∃ U ∈ 𝓝 z,
      {α ∈ catalogue | (U ∩ cut (slantDir κ) α).Nonempty}.Finite := by
    intro z hz
    let ε : ℝ := (z.re - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; have : 1 < z.re := hz; linarith
    let K : Set ℂ := closedBall z (ε + ‖slantDir κ‖) ∩ {α | z.re - ε ≤ α.re}
    have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const Complex.continuous_re)
    have hKH : K ⊆ HH := by
      rintro α ⟨_, hα⟩
      change 1 < α.re
      change z.re - ε ≤ α.re at hα
      dsimp [ε] at *
      have : 1 < z.re := hz
      linarith
    refine ⟨ball z ε, ball_mem_nhds _ hε,
      (geometry_catalogue_finite_compact hK hKH).subset ?_⟩
    rintro α ⟨hα, s, hsball, t, ht, htα, he⟩
    have ht1 : t ≤ 1 := by linarith [re_le_two_of_mem_catalogue hα]
    have hdist : dist α s = t * ‖slantDir κ‖ := by
      rw [he, dist_eq_norm]
      have : α - (α - (t : ℂ) * slantDir κ) = (t : ℂ) * slantDir κ := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hsre := re_gt_of_mem_ball hsball
    have hsr : s.re = α.re - t := by rw [he]; simp [slantDir]
    refine ⟨⟨?_, ?_⟩, hα⟩
    · change dist α z ≤ ε + ‖slantDir κ‖
      have hsz : dist s z < ε := hsball
      have htv : t * ‖slantDir κ‖ ≤ ‖slantDir κ‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht1
      calc
        dist α z ≤ dist α s + dist s z := dist_triangle _ _ _
        _ ≤ ε + ‖slantDir κ‖ := by rw [hdist]; linarith
    · change z.re - ε ≤ α.re
      linarith
  refine ⟨hlocal, isOpen_iff_mem_nhds.mpr ?_⟩
  intro z hz
  obtain ⟨U, hU, hf⟩ := hlocal z hz.1
  let A := {α ∈ catalogue | (U ∩ cut (slantDir κ) α).Nonempty}
  have havoid : ∀ᶠ s in 𝓝 z, ∀ α ∈ A, s ∈ HH \ cut (slantDir κ) α := by
    apply (Filter.eventually_all_finite hf).mpr
    intro α hα
    apply (geometry_isOpen_diff_cut κ α).mem_nhds
    exact ⟨hz.1, fun h => hz.2 (mem_iUnion₂.mpr ⟨α, hα.1, h⟩)⟩
  filter_upwards [hU, havoid,
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1] with s hsU hsA hsH
  refine ⟨hsH, ?_⟩
  intro hcut
  obtain ⟨α, hα, hsα⟩ := mem_iUnion₂.mp hcut
  exact (hsA α ⟨hα, s, hsU, hsα⟩).2 hsα

end GoldbachBoundaries.ThmA
