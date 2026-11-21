import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Σ_Q` is locally finite in `Re z > 0` (no RH). The proof of the second part of `lem_Sigma_iv_proof`
(`SigmaFinite.lean`) does not use RH and is reused here, with meromorphicity at `1` as well. -/
theorem poleSetQ_locallyFinite : ∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite := by
  intro z hz
  simp only [halfPlane, mem_ofPred_eq] at hz
  set x := z.re with hx
  refine ⟨ball z (x / 2), ball_mem_nhds z (by linarith), ?_⟩
  have hre : ∀ w ∈ ball z (x / 2), x / 2 < w.re := fun w hw => by
    have := re_gt_of_mem_ball hw; linarith
  -- the three pieces
  have hA : (ball z (x / 2) ∩ {1}).Finite := (finite_singleton 1).subset inter_subset_right
  have hB : (ball z (x / 2) ∩
      {w | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ w = 1 / (k : ℂ)}).Finite := by
    refine ((finite_Iio (⌈2 / x⌉₊ + 1)).image (fun k : ℕ => 1 / (k : ℂ))).subset ?_
    rintro w ⟨hwb, k, hk, -, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have h := hre _ hwb
    rw [re_one_div_natCast] at h
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hk2 : (k : ℝ) < 2 / x := by
      rw [lt_div_iff₀ hz]
      rw [lt_div_iff₀ hkpos] at h
      linarith
    have : (k : ℝ) < ⌈2 / x⌉₊ := lt_of_lt_of_le hk2 (Nat.le_ceil _)
    have : k < ⌈2 / x⌉₊ := by exact_mod_cast this
    simp only [mem_Iio]; omega
  have hC : (ball z (x / 2) ∩ {w | ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧
      ∃ ρ ∈ NontrivialZeros, w = ρ / (n : ℂ)}).Finite := by
    let K : ℕ → Set ℂ := fun n =>
      closedBall ((n : ℂ) * z) ((n : ℝ) * (x / 2))
    have hK : ∀ n, (K n ∩ {s | riemannZeta s = 0}).Finite := by
      intro n
      have hc := (isCompact_closedBall ((n : ℂ) * z) ((n : ℝ) * (x / 2))).finite_sdiff_of_mem_codiscreteWithin
        ((show MeromorphicOn riemannZeta (K n) from fun w _ => meromorphicAt_riemannZeta w).eventually_codiscreteWithin_apply_ne_zero
          (fun w _ => meromorphicOrderAt_riemannZeta_ne_top w))
      exact hc.subset (by intro w hw; exact ⟨hw.1, by simpa using hw.2⟩)
    refine (Set.Finite.biUnion (finite_Iio (⌈2 / x⌉₊ + 1)) fun n _ =>
      (hK n).image (fun ρ => ρ / (n : ℂ))).subset ?_
    rintro w ⟨hwb, n, hn, -, ρ, hρ, rfl⟩
    refine mem_iUnion₂.mpr ⟨n, ?_, ρ, ⟨?_, hρ.1⟩, rfl⟩
    · have h := hre _ hwb
      rw [Complex.div_natCast_re] at h
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn1 : (n : ℝ) < 2 / x := by
        rw [lt_div_iff₀ hz]
        rw [lt_div_iff₀ hnpos] at h
        linarith [hρ.2.2]
      have : (n : ℝ) < ⌈2 / x⌉₊ := lt_of_lt_of_le hn1 (Nat.le_ceil _)
      have : n < ⌈2 / x⌉₊ := by exact_mod_cast this
      simp only [mem_Iio]; omega
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hd : dist (ρ / n) z < x / 2 := mem_ball.mp hwb
      rw [mem_closedBall, dist_eq_norm]
      have : ρ - (n : ℂ) * z = (n : ℂ) * (ρ / n - z) := by field_simp
      rw [this, norm_mul, Complex.norm_natCast, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hd.le hnpos.le
  refine ((hA.union hB).union hC).subset ?_
  rintro w ⟨hwb, (h1 | h2) | h3⟩
  · exact Or.inl (Or.inl ⟨hwb, h1⟩)
  · exact Or.inl (Or.inr ⟨hwb, h2⟩)
  · exact Or.inr ⟨hwb, h3⟩

end GoldbachBoundaries.Paper2.M1
