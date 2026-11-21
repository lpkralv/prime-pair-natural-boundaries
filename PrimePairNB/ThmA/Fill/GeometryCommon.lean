import PrimePairNB.ThmA.G14_Geometry
import PrimePairNB.ThmA.Fill.catalogue_locallyFinite
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

lemma geometry_mem_cut_iff (κ : ℝ) {α s : ℂ} (hs : s ∈ HH) :
    s ∈ cut (slantDir κ) α ↔
      ((s - α) / slantDir κ).re ≤ 0 ∧ ((s - α) / slantDir κ).im = 0 := by
  have hv := slantDir_ne_zero κ
  constructor
  · rintro ⟨t, ht, _, rfl⟩
    have he : (α - (t : ℂ) * slantDir κ - α) / slantDir κ = -(t : ℂ) := by
      field_simp
      ring
    rw [he]
    simpa using ht
  · rintro ⟨hre, him⟩
    let q := (s - α) / slantDir κ
    have hreal : q = (q.re : ℂ) := Complex.ext (by simp) (by simpa [q] using him)
    have he : s = α - ((-q.re : ℝ) : ℂ) * slantDir κ := by
      have hid : q * slantDir κ = s - α := div_mul_cancel₀ _ hv
      rw [hreal] at hid
      push_cast
      linear_combination -hid
    refine ⟨-q.re, neg_nonneg.mpr hre, ?_, he⟩
    have heR := congrArg Complex.re he
    simp [slantDir] at heR
    have : 1 < s.re := hs
    linarith

lemma geometry_isOpen_diff_cut (κ : ℝ) (α : ℂ) :
    IsOpen (HH \ cut (slantDir κ) α) := by
  have he : HH \ cut (slantDir κ) α =
      HH ∩ (fun s => (s - α) / slantDir κ) ⁻¹' slitPlane := by
    ext s
    by_cases hs : s ∈ HH
    · simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, hs, true_and,
        geometry_mem_cut_iff κ hs, Complex.mem_slitPlane_iff]
      simp only [not_and_or, not_le]
    · simp [hs]
  rw [he]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_slitPlane.preimage (by fun_prop))

lemma geometry_catalogue_finite_compact {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ HH) :
    (K ∩ catalogue).Finite := by
  classical
  let U : ℂ → Set ℂ := fun z =>
    if hz : z ∈ HH then (catalogue_locallyFinite.1 z hz).choose else univ
  have hU : ∀ z ∈ K, U z ∈ 𝓝 z := by
    intro z hz
    simp only [U, hKH hz, dite_true]
    exact (catalogue_locallyFinite.1 z (hKH hz)).choose_spec.1
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover U hU
  have hf : (⋃ z ∈ t, U z ∩ catalogue).Finite := by
    refine t.finite_toSet.biUnion fun z hz => ?_
    simp only [U, hKH (htK z hz), dite_true]
    exact (catalogue_locallyFinite.1 z (hKH (htK z hz))).choose_spec.2
  apply hf.subset
  rintro s ⟨hsK, hsC⟩
  obtain ⟨z, hz, hsz⟩ := mem_iUnion₂.mp (hcover hsK)
  exact mem_iUnion₂.mpr ⟨z, hz, hsz, hsC⟩

end GoldbachBoundaries.ThmA
