import PrimePairNB.ThmA.G14_Geometry
import Mathlib.NumberTheory.LSeries.ZetaZeros

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

-- The bounded-denominator argument of SigmaFinite.lean, using Re ρ < 1 rather than RH.
/-- `𝒞` is locally finite in `ℍ`; equivalently, discrete and closed in `ℍ`.

Sketch. Near `z` with `Re z = 1 + 2ε`, points of `𝒞` with real part `≥ 1 + ε` are `2`, `1 + 1/k`
with `k ≤ 1/ε`, and `1 + ρ/n` with `Re ρ/n ≥ ε`, so `n < 1/ε` (as `Re ρ < 1`) and `ρ` in a bounded
set: finitely many (`riemannZeta_zeros_finite_of_isCompact`, `SigmaFinite.lean`; follow the proof
of `lem_Sigma_iv_proof` with `Re ρ < 1` in place of `Re ρ = 1/2`). The second and third conjuncts
follow (`mem_codiscreteWithin`, `isOpen_iff`). -/
theorem catalogue_locallyFinite :
    (∀ z ∈ HH, ∃ U ∈ 𝓝 z, (U ∩ catalogue).Finite) ∧
    (∀ᶠ z in codiscreteWithin HH, z ∉ catalogue) ∧ IsOpen (HH \ catalogue) := by
  have hlocal : ∀ z ∈ HH, ∃ U ∈ 𝓝 z, (U ∩ catalogue).Finite := by
    intro z hz
    have hx : 0 < z.re - 1 := sub_pos.mpr hz
    set x := z.re - 1 with hxdef
    refine ⟨ball z (x / 2), ball_mem_nhds _ (by positivity), ?_⟩
    have hre : ∀ w ∈ ball z (x / 2), x / 2 < w.re - 1 := by
      intro w hw
      have := re_gt_of_mem_ball hw
      dsimp [x] at *
      linarith
    have hA : (ball z (x / 2) ∩ {2}).Finite :=
      (finite_singleton _).subset inter_subset_right
    have hB : (ball z (x / 2) ∩
        {w | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ w = 1 + 1 / (k : ℂ)}).Finite := by
      refine ((finite_Iio (⌈2 / x⌉₊ + 1)).image
        (fun k : ℕ => 1 + 1 / (k : ℂ))).subset ?_
      rintro w ⟨hw, k, hk, _, rfl⟩
      refine ⟨k, ?_, rfl⟩
      have h := hre _ hw
      simp only [Complex.add_re, Complex.one_re, re_one_div_natCast,
        add_sub_cancel_left] at h
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hk2 : (k : ℝ) < 2 / x := by
        rw [lt_div_iff₀ hx]
        rw [lt_div_iff₀ hkpos] at h
        linarith
      have : (k : ℝ) < ⌈2 / x⌉₊ := lt_of_lt_of_le hk2 (Nat.le_ceil _)
      have : k < ⌈2 / x⌉₊ := by exact_mod_cast this
      simp only [mem_Iio]
      omega
    have hC : (ball z (x / 2) ∩ {w | ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧
        ∃ ρ ∈ NontrivialZeros, w = 1 + ρ / (n : ℂ)}).Finite := by
      let K : ℕ → Set ℂ := fun n =>
        closedBall ((n : ℂ) * (z - 1)) ((n : ℝ) * (x / 2))
      have hK : ∀ n, (K n ∩ riemannZetaZeros).Finite := fun n =>
        (isCompact_closedBall _ _).inter_riemannZetaZeros_finite
      refine (Set.Finite.biUnion (finite_Iio (⌈2 / x⌉₊ + 1)) fun n _ =>
        (hK n).image (fun ρ => 1 + ρ / (n : ℂ))).subset ?_
      rintro w ⟨hw, n, hn, _, ρ, hρ, rfl⟩
      refine mem_iUnion₂.mpr ⟨n, ?_, ρ, ⟨?_, hρ.1⟩, rfl⟩
      · have h := hre _ hw
        simp only [Complex.add_re, Complex.one_re, Complex.div_natCast_re,
          add_sub_cancel_left] at h
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hn2 : (n : ℝ) < 2 / x := by
          rw [lt_div_iff₀ hx]
          rw [lt_div_iff₀ hnpos] at h
          linarith [hρ.2.2]
        have : (n : ℝ) < ⌈2 / x⌉₊ := lt_of_lt_of_le hn2 (Nat.le_ceil _)
        have : n < ⌈2 / x⌉₊ := by exact_mod_cast this
        simp only [mem_Iio]
        omega
      · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have hnpos : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have hd : ‖1 + ρ / (n : ℂ) - z‖ < x / 2 := by
          simpa only [dist_eq_norm] using mem_ball.mp hw
        change dist ρ ((n : ℂ) * (z - 1)) ≤ (n : ℝ) * (x / 2)
        rw [dist_eq_norm]
        have he : ρ - (n : ℂ) * (z - 1) = (n : ℂ) * (1 + ρ / n - z) := by
          field_simp
          ring
        rw [he, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hd.le hnpos
    refine ((hA.union hB).union hC).subset ?_
    rintro w ⟨hw, (h1 | h2) | h3⟩
    · exact Or.inl (Or.inl ⟨hw, h1⟩)
    · exact Or.inl (Or.inr ⟨hw, h2⟩)
    · exact Or.inr ⟨hw, h3⟩
  refine ⟨hlocal, ?_, ?_⟩
  · apply codiscreteWithin_iff_locallyFiniteComplementWithin.mpr
    intro z hz
    obtain ⟨U, hU, hf⟩ := hlocal z hz
    exact ⟨U, hU, hf.subset (by intro s hs; exact ⟨hs.1, not_not.mp hs.2.2⟩)⟩
  · apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨hzH, hzC⟩
    obtain ⟨U, hU, hf⟩ := hlocal z hzH
    have hH : HH ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzH
    have hc : (U ∩ catalogue)ᶜ ∈ 𝓝 z := hf.isClosed.isOpen_compl.mem_nhds (by
      intro hz; exact hzC hz.2)
    exact mem_of_superset (inter_mem (inter_mem hU hH) hc) (by
      rintro w ⟨⟨hwU, hwH⟩, hwc⟩
      exact ⟨hwH, fun hwC => hwc ⟨hwU, hwC⟩⟩)

end GoldbachBoundaries.ThmA
