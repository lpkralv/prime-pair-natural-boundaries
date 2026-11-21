import PrimePairNB.ThmA.G14_Geometry
import PrimePairNB.ThmA.Fill.GeometryCommon
import PrimePairNB.ThmA.Fill.cuts_locallyFinite

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

private lemma geometry_avoid_other_cuts {κ : ℝ} {α p : ℂ} (hp : p ∈ HH)
    (havoid : ∀ α' ∈ catalogue, α' ≠ α → p ∉ cut (slantDir κ) α') :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ HH ∧
      ∀ α' ∈ catalogue, α' ≠ α → Disjoint (ball p r) (cut (slantDir κ) α') := by
  obtain ⟨U, hU, hf⟩ := (cuts_locallyFinite κ).1 p hp
  let A := {α' ∈ catalogue | (U ∩ cut (slantDir κ) α').Nonempty}
  have hav : ∀ᶠ s in 𝓝 p, ∀ α' ∈ A, α' ≠ α → s ∉ cut (slantDir κ) α' := by
    apply (Filter.eventually_all_finite hf).mpr
    intro α' hα'
    by_cases he : α' = α
    · exact Filter.Eventually.of_forall (by intro s h; exact False.elim (h he))
    · filter_upwards [(geometry_isOpen_diff_cut κ α').mem_nhds
        ⟨hp, havoid α' hα'.1 he⟩] with s hs
      exact fun _ => hs.2
  have hnh : {s | s ∈ U ∧ s ∈ HH ∧ ∀ α' ∈ A, α' ≠ α → s ∉ cut (slantDir κ) α'} ∈ 𝓝 p := by
    filter_upwards [hU, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp,
      hav] with s hsU hsH hsav
    exact ⟨hsU, hsH, hsav⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨r, hr, fun s hs => (hsub hs).2.1, ?_⟩
  intro α' hα' hne
  apply Set.disjoint_left.mpr
  intro s hs hsα'
  have hsU := (hsub hs).1
  exact (hsub hs).2.2 α' ⟨hα', s, hsU, hsα'⟩ hne hsα'

/-- Small discs about catalogue points and about cut points.

Sketch. Good slant: `α ∉ cut_{α'}` for `α' ≠ α`, and cuts are pairwise disjoint (a common point
would give two catalogue points differing by a real multiple of `v`). Each `cut_{α'}` is closed in
`ℍ` and only finitely many meet a neighbourhood, so a small ball about `α` (resp. about
`s₀ ∈ cut_α`, `s₀ ≠ α`) misses all other cuts; shrink so the ball lies in `ℍ`
(`r ≤ Re α - 1`) and, for `s₀`, so that `α ∉ ball s₀ r`. For the first part, a point of the ball off
`cut_α` lies on no cut, so in `Ω_ℍ`. -/
theorem exists_good_discs {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ} (hα : α ∈ catalogue) :
    (∃ r : ℝ, 0 < r ∧ r ≤ α.re - 1 ∧ slitDisc (slantDir κ) α r ⊆ Omega κ) ∧
    (∀ s₀ ∈ cut (slantDir κ) α, s₀ ≠ α → ∃ r : ℝ, 0 < r ∧ IsCutDisc κ α s₀ r) := by
  have hαH : α ∈ HH := one_lt_re_of_mem_catalogue hα
  constructor
  · obtain ⟨δ, hδ, hδH, hδav⟩ := geometry_avoid_other_cuts hαH (by
      intro α' hα' hne hcut
      exact hne (catalogue_inter_cut hκ hα' hcut hα).symm)
    let r := min δ (α.re - 1)
    have hr : 0 < r := lt_min hδ (sub_pos.mpr hαH)
    refine ⟨r, hr, min_le_right _ _, ?_⟩
    rintro s ⟨hsball, hsnot⟩
    have hsδ : s ∈ ball α δ := ball_subset_ball (min_le_left _ _) hsball
    refine ⟨hδH hsδ, ?_⟩
    intro hcut
    obtain ⟨α', hα', hsα'⟩ := mem_iUnion₂.mp hcut
    by_cases he : α' = α
    · exact hsnot (he ▸ hsα')
    · exact Set.disjoint_left.mp (hδav α' hα' he) hsδ hsα'
  · intro s₀ hs₀ hne₀
    obtain ⟨t, ht, htα, he₀⟩ := hs₀
    have hsH : s₀ ∈ HH := by
      change 1 < s₀.re
      rw [he₀]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        slantDir, Complex.add_re, Complex.one_re, Complex.I_re, mul_zero, sub_zero,
        mul_one, zero_mul, add_zero]
      linarith
    obtain ⟨δ, hδ, hδH, hδav⟩ := geometry_avoid_other_cuts hsH (by
      intro α' hα' hne hsα'
      obtain ⟨u, _, _, he'⟩ := hsα'
      apply hκ.2.2 α hα α' hα' (Ne.symm hne) (t - u)
      push_cast
      linear_combination he' - he₀)
    let r := min δ (dist α s₀)
    have hr : 0 < r := lt_min hδ (dist_pos.mpr (Ne.symm hne₀))
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · exact (ball_subset_ball (min_le_left _ _)).trans hδH
    · intro hball
      have := mem_ball.mp hball
      exact (not_lt_of_ge (min_le_right δ (dist α s₀))) this
    · intro α' hα' hne
      exact (hδav α' hα' hne).mono_left (ball_subset_ball (min_le_left _ _))

end GoldbachBoundaries.ThmA
