import PrimePairNB.ThmA.Defs

/-!
# Geometry of the catalogue and the slanted cuts (the slant lemma, the cuts lemma)

All statements here are unconditional (no RH): `catalogue` is defined without RH, and the
facts used (`Re ρ ∈ (0,1)`, zeros of `ζ` locally finite) hold unconditionally.

The lemmas `catalogue_countable`, `exists_goodSlant_of_countable`, `catalogue_locallyFinite`,
`cuts_locallyFinite`, `isPreconnected_Omega_inter`, `exists_good_discs`, `cutDisc_facts`,
`slitDisc_facts` are proved in `Fill/<name>.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

theorem slantDir_ne_zero (κ : ℝ) : slantDir κ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [slantDir] at this

theorem ball_subset_HH {α : ℂ} {r : ℝ} (hr : r ≤ α.re - 1) : ball α r ⊆ HH := by
  intro s hs
  have h1 : |s.re - α.re| ≤ ‖s - α‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : ‖s - α‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hs
  have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
  show (1 : ℝ) < s.re
  linarith

theorem mem_cut_self {κ : ℝ} {α : ℂ} (hα : 1 < α.re) : α ∈ cut (slantDir κ) α :=
  ⟨0, le_rfl, by linarith, by simp⟩

theorem one_lt_re_of_mem_catalogue {α : ℂ} (hα : α ∈ catalogue) : 1 < α.re := by
  rcases hα with (hs | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · rw [mem_singleton_iff.mp hs]; norm_num
  · have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have : (1 + 1 / (k : ℂ)).re = 1 + 1 / (k : ℝ) := by simp [Complex.normSq_natCast]
    rw [this]
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have : (1 + ρ / (n : ℂ)).re = 1 + ρ.re / n := by simp [Complex.div_natCast_re]
    rw [this]
    have : 0 < ρ.re / n := div_pos hρ.2.1 hn'
    linarith

theorem re_le_two_of_mem_catalogue {α : ℂ} (hα : α ∈ catalogue) : α.re ≤ 2 := by
  rcases hα with (hs | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · rw [mem_singleton_iff.mp hs]; norm_num
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : (1 + 1 / (k : ℂ)).re = 1 + 1 / (k : ℝ) := by simp [Complex.normSq_natCast]
    rw [this]
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 + ρ / (n : ℂ)).re = 1 + ρ.re / n := by simp [Complex.div_natCast_re]
    rw [this]
    have : ρ.re / n ≤ ρ.re := div_le_self hρ.2.1.le hn'
    linarith [hρ.2.2]

theorem Omega_subset {κ : ℝ} : Omega κ ⊆ HH \ catalogue := by
  rintro s ⟨hsH, hs⟩
  refine ⟨hsH, fun hsC => hs ?_⟩
  exact mem_biUnion hsC (mem_cut_self (one_lt_re_of_mem_catalogue hsC))

theorem halfPlane_two_subset_Omega (κ : ℝ) : halfPlane 2 ⊆ Omega κ := by
  intro s hs
  have hs' : (2 : ℝ) < s.re := hs
  refine ⟨show (1 : ℝ) < s.re by linarith, ?_⟩
  simp only [mem_iUnion, not_exists]
  rintro α hα ⟨t, ht0, -, rfl⟩
  have h2 := re_le_two_of_mem_catalogue hα
  have : (α - (t : ℂ) * slantDir κ).re = α.re - t := by simp [slantDir]
  rw [this] at hs'
  linarith

/-- On a cut, the only catalogue point is its start (good slant). -/
theorem catalogue_inter_cut {κ : ℝ} (hκ : IsGoodSlant κ) {α s : ℂ} (hα : α ∈ catalogue)
    (hs : s ∈ cut (slantDir κ) α) (hsC : s ∈ catalogue) : s = α := by
  by_contra hne
  obtain ⟨t, -, -, rfl⟩ := hs
  exact hκ.2.2 α hα _ hsC (Ne.symm hne) t (by ring)

theorem mem_Omega_or_mem_cut {κ : ℝ} {p : ℂ} (hp : p ∈ HH \ catalogue) :
    p ∈ Omega κ ∨ ∃ α ∈ catalogue, p ∈ cut (slantDir κ) α ∧ p ≠ α := by
  by_cases h : p ∈ Omega κ
  · exact Or.inl h
  · right
    have : p ∈ ⋃ α ∈ catalogue, cut (slantDir κ) α := by
      by_contra h'
      exact h ⟨hp.1, h'⟩
    obtain ⟨α, hα, hpα⟩ := mem_iUnion₂.mp this
    exact ⟨α, hα, hpα, fun he => hp.2 (he ▸ hα)⟩

theorem slitDisc_mono {v α : ℂ} {r r' : ℝ} (h : r ≤ r') : slitDisc v α r ⊆ slitDisc v α r' :=
  sdiff_subset_sdiff_left (ball_subset_ball h)

/-- A point of the slit disc (on the side opposite the cut). -/
theorem exists_mem_slitDisc (κ : ℝ) {α : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ s, s ∈ slitDisc (slantDir κ) α r ∧ (s - α) / slantDir κ ∈ slitPlane := by
  have hv := slantDir_ne_zero κ
  have hnv : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hv
  set c : ℝ := r / (2 * ‖slantDir κ‖) with hc
  have hc0 : 0 < c := by positivity
  have hq : (α + (c : ℂ) * slantDir κ - α) / slantDir κ = c := by field_simp; ring
  refine ⟨α + (c : ℂ) * slantDir κ, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc0, hc]
    field_simp
    linarith
  · rintro ⟨t, ht, -, he⟩
    have : (c : ℂ) * slantDir κ = -((t : ℂ) * slantDir κ) := by linear_combination he
    have h2 := congrArg Complex.re this
    simp [slantDir] at h2
    linarith
  · rw [hq]; exact Complex.ofReal_mem_slitPlane.mpr hc0

end GoldbachBoundaries.ThmA
