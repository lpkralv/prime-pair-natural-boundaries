import PrimePairNB.Paper2.M2.Rigidity

/-! `singlePairs_bounds` of `Paper2/M2/Single.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `X / M(X) → ∞`: for every `K > 0`, eventually `K ≤ X / M(X)` (and `M(X) ≥ 1`). -/
lemma singlePairs_bounds_le_div_Mfun {A₀ : ℝ} (hA₀ : 0 < A₀) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ X in atTop, K ≤ X / (Mfun A₀ X : ℝ) := by
  have hlo := Real.isLittleO_log_id_atTop.def (c := A₀ / (4 * K)) (by positivity)
  filter_upwards [hlo, Filter.eventually_ge_atTop (2 * K), Filter.eventually_gt_atTop (1 : ℝ)]
    with X hX hX2 hX1
  have hlog : 0 < Real.log X := Real.log_pos hX1
  simp only [Real.norm_eq_abs, id, abs_of_pos hlog, abs_of_pos (by linarith : (0 : ℝ) < X)] at hX
  have hM1 : (Mfun A₀ X : ℝ) ≤ 2 * Real.log X / A₀ + 1 := by
    unfold Mfun
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * Real.log X / A₀)
    linarith
  have hM2 : 2 * Real.log X / A₀ ≤ X / (2 * K) := by
    rw [div_le_div_iff₀ hA₀ (by positivity)]
    have : Real.log X * (4 * K) ≤ A₀ * X := by
      have := hX
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      linarith
    nlinarith
  have hMpos : (0 : ℝ) < Mfun A₀ X := by
    unfold Mfun
    have : 0 < 2 * Real.log X / A₀ := by positivity
    exact_mod_cast Nat.ceil_pos.mpr this
  have hMle : (Mfun A₀ X : ℝ) ≤ X / K := by
    have : X / (2 * K) + 1 ≤ X / K := by
      rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hK]
      nlinarith
    linarith
  rw [le_div_iff₀ hMpos]
  rw [le_div_iff₀ hK] at hMle
  linarith

/-- **Every pair of `𝓟(X)` is close to `iy`** (unconditional; part (b) without the residue). For large `X`, every
`p = (ρ, q) ∈ 𝓟(X)` has `q > γ/(y + ε/2) > X/(M(y + ε/2)) > 1/ε` (the last for large `X`, as `M ≪ log X`), so
`|u - iy| ≤ 1/(2q) + |γ/q - y| < ε/2 + ε/2`; `Re u = Re ρ/q = 1/(2q)`; and `|ρ| = (1/4 + γ²)^{1/2} ≤ X + 1`,
`m(ρ) ≥ 1` (`one_le_zetaMult`), so `2/(X + 1) ≤ 2m(ρ)/|ρ|`. -/
theorem singlePairs_bounds {A₀ y ε : ℝ} (hA₀ : 0 < A₀) (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∀ᶠ X in atTop, ∀ p ∈ singlePairs A₀ y ε X,
      ‖p.1 / (p.2 : ℂ) - y * I‖ < ε ∧ (p.1 / (p.2 : ℂ)).re = 1 / (2 * p.2) ∧
        2 / (X + 1) ≤ 2 * zetaMult p.1 / ‖p.1‖ := by
  have hK : 0 < (y + ε / 2) / ε := by positivity
  filter_upwards [singlePairs_bounds_le_div_Mfun hA₀ _ hK, Filter.eventually_ge_atTop (1 : ℝ)] with X hXM hX1
  rintro ⟨ρ, q⟩ ⟨hρ, hre, hlo, hhi, hq, hJ1, hJ2⟩
  simp only at hρ hre hlo hhi hq hJ1 hJ2 ⊢
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hyε : 0 < y + ε / 2 := by positivity
  have hγ : ρ.im < q * (y + ε / 2) := by
    rw [div_lt_iff₀ hqR] at hJ2; linarith
  -- `q ε > 1`
  have hqε : 1 < q * ε := by
    have h1 : (y + ε / 2) / ε < q * (y + ε / 2) := lt_of_le_of_lt hXM (hlo.trans hγ)
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  have hre' : (ρ / (q : ℂ)).re = 1 / (2 * q) := by
    rw [Complex.div_natCast_re, hre]; field_simp
  have him' : (ρ / (q : ℂ)).im = ρ.im / q := by rw [Complex.div_natCast_im]
  refine ⟨?_, hre', ?_⟩
  · have hle := Complex.norm_le_abs_re_add_abs_im (ρ / (q : ℂ) - y * I)
    have hr : (ρ / (q : ℂ) - y * I).re = 1 / (2 * q) := by simp [hre']
    have hi : (ρ / (q : ℂ) - y * I).im = ρ.im / q - y := by simp [him']
    rw [hr, hi] at hle
    have h1 : |1 / (2 * (q : ℝ))| < ε / 2 := by
      rw [abs_of_pos (by positivity), div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : |ρ.im / q - y| < ε / 2 := by
      rw [abs_lt]; constructor <;> linarith
    linarith
  · have hm : (1 : ℝ) ≤ zetaMult ρ := by exact_mod_cast one_le_zetaMult hρ
    have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_mem_nontrivialZeros hρ)
    have hnorm : ‖ρ‖ ≤ X + 1 := by
      have := Complex.norm_le_abs_re_add_abs_im ρ
      rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      have him0 : 0 < ρ.im := lt_of_le_of_lt (by positivity) hlo
      rw [abs_of_pos him0] at this
      linarith
    calc 2 / (X + 1) ≤ 2 / ‖ρ‖ := div_le_div_of_nonneg_left (by norm_num) hρ0 hnorm
      _ ≤ 2 * zetaMult ρ / ‖ρ‖ := by
        apply div_le_div_of_nonneg_right _ hρ0.le
        linarith

end GoldbachBoundaries.Paper2.M2
