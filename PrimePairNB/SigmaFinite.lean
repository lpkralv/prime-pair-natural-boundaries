import PrimePairNB.Defs

/-!
# The pole set `Σ` of `Q` under RH

Under RH:

* `Σ ∩ {Re z > 1/2} = {1}`: `Re(1/k) = 1/k ≤ 1/2` for `k ≥ 2` and `Re(ρ/n) = 1/(2n) ≤ 1/2`;
* `Σ` is locally finite in `Re z > 0`: on the ball `B(z, x/2)`, `x = Re z`, every point has real
  part `> x/2`, so only `1/k` with `k < 2/x` and `ρ/n` with `n < 1/x` can occur, and for each such
  `n` the zeros `ρ` lie in the compact set `closedBall (n z) (n x/2) ∩ {Re = 1/2}`, which avoids
  `s = 1`. Zeros of `ζ` in a compact subset of `ℂ ∖ {1}` are finitely many, because `ζ` is
  analytic and not identically zero on the connected open set `ℂ ∖ {1}`
  (Mathlib's `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- Under RH a zero of `ζ` with positive real part lies on the critical line. -/
lemma sigmaFinite_re_eq_half (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ.re = 1 / 2 := by
  refine hRH ρ hρ.1 ?_ ?_
  · rintro ⟨n, rfl⟩
    have h := hρ.2.1
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hρ.1

/-- `ζ` is analytic on `ℂ ∖ {1}`. -/
lemma analyticOnNhd_riemannZeta_compl_one : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- The zeros of `ζ` are locally finite in `ℂ ∖ {1}`. -/
lemma riemannZeta_zeros_locallyFinite :
    ∀ w ∈ ({1}ᶜ : Set ℂ), ∃ t ∈ 𝓝 w,
      (t ∩ ({1}ᶜ \ (riemannZeta ⁻¹' {0}ᶜ))).Finite := by
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) _
  have h2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hcod := analyticOnNhd_riemannZeta_compl_one.preimage_zero_mem_codiscreteWithin h2 hmem hconn
  exact (codiscreteWithin_iff_locallyFiniteComplementWithin.mp hcod)

/-- Finitely many zeros of `ζ` lie in a compact set avoiding `1`. -/
lemma riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) (h1 : (1 : ℂ) ∉ K) :
    (K ∩ {s | riemannZeta s = 0}).Finite := by
  classical
  have hloc := riemannZeta_zeros_locallyFinite
  let U : ℂ → Set ℂ := fun w =>
    if hw : w ∈ ({1}ᶜ : Set ℂ) then (hloc w hw).choose else univ
  have hU : ∀ w ∈ K, U w ∈ 𝓝 w := by
    intro w hw
    have hw1 : w ∈ ({1}ᶜ : Set ℂ) := fun h => h1 (by rw [mem_singleton_iff.mp h] at hw; exact hw)
    simp only [U, hw1, dite_true]
    exact (hloc w hw1).choose_spec.1
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover U hU
  have hfin : (⋃ w ∈ t, (U w ∩ ({1}ᶜ \ (riemannZeta ⁻¹' {0}ᶜ)))).Finite := by
    refine Set.Finite.biUnion t.finite_toSet ?_
    intro w hw
    have hw1 : w ∈ ({1}ᶜ : Set ℂ) :=
      fun h => h1 (by have := htK w hw; rw [mem_singleton_iff.mp h] at this; exact this)
    simp only [U, hw1, dite_true]
    exact (hloc w hw1).choose_spec.2
  refine hfin.subset ?_
  rintro s ⟨hsK, hs0⟩
  obtain ⟨w, hw, hsw⟩ := mem_iUnion₂.mp (hcover hsK)
  refine mem_iUnion₂.mpr ⟨w, hw, hsw, ?_, ?_⟩
  · intro h; exact h1 (by rw [mem_singleton_iff.mp h] at hsK; exact hsK)
  · simpa using hs0

/-- Real part of `1 / k`. -/
lemma re_one_div_natCast (k : ℕ) : (1 / (k : ℂ)).re = 1 / (k : ℝ) := by
  rw [Complex.div_natCast_re]; simp

/-- Points of a ball `B(z, r)` have real part `> Re z - r`. -/
lemma re_gt_of_mem_ball {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) : z.re - r < w.re := by
  have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : ‖w - z‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hw
  have h3 := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
  linarith

/-- Under RH, `Σ ∩ {Re z > 1/2} = {1}` and `Σ` is locally finite in `Re z > 0`. -/
theorem lem_Sigma_iv_proof (hRH : RiemannHypothesis) :
    PoleSetQ ∩ halfPlane (1 / 2) = {1} ∧
      ∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite := by
  refine ⟨?_, ?_⟩
  · -- part 1: only `1` survives in `Re z > 1/2`
    ext w
    simp only [mem_inter_iff, mem_singleton_iff, halfPlane, mem_ofPred_eq]
    constructor
    · rintro ⟨(hw | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩, hre⟩
      · exact mem_singleton_iff.mp hw
      · exfalso
        rw [re_one_div_natCast] at hre
        have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
        have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
        linarith
      · exfalso
        rw [Complex.div_natCast_re, sigmaFinite_re_eq_half hRH hρ] at hre
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have : 1 / 2 / (n : ℝ) ≤ 1 / 2 := div_le_self (by norm_num) hn'
        linarith
    · rintro rfl
      exact ⟨Or.inl (Or.inl rfl), by norm_num⟩
  · -- part 2: local finiteness in `Re z > 0`
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
        closedBall ((n : ℂ) * z) ((n : ℝ) * (x / 2)) ∩ {s | s.re = 1 / 2}
      have hK : ∀ n, (K n ∩ {s | riemannZeta s = 0}).Finite := by
        intro n
        refine riemannZeta_zeros_finite_of_isCompact ?_ ?_
        · exact (isCompact_closedBall _ _).inter_right
            (isClosed_eq Complex.continuous_re continuous_const)
        · rintro ⟨-, h⟩
          simp only [mem_ofPred_eq, one_re] at h
          norm_num at h
      refine (Set.Finite.biUnion (finite_Iio (⌈1 / x⌉₊ + 1)) fun n _ =>
        (hK n).image (fun ρ => ρ / (n : ℂ))).subset ?_
      rintro w ⟨hwb, n, hn, -, ρ, hρ, rfl⟩
      refine mem_iUnion₂.mpr ⟨n, ?_, ρ, ⟨⟨?_, sigmaFinite_re_eq_half hRH hρ⟩, hρ.1⟩, rfl⟩
      · have h := hre _ hwb
        rw [Complex.div_natCast_re, sigmaFinite_re_eq_half hRH hρ] at h
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hn1 : (n : ℝ) < 1 / x := by
          rw [lt_div_iff₀ hz]
          rw [lt_div_iff₀ hnpos] at h
          linarith
        have : (n : ℝ) < ⌈1 / x⌉₊ := lt_of_lt_of_le hn1 (Nat.le_ceil _)
        have : n < ⌈1 / x⌉₊ := by exact_mod_cast this
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

end GoldbachBoundaries
