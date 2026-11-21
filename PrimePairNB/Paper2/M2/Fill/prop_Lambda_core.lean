import PrimePairNB.Paper2.M2.Far
import PrimePairNB.Paper2.M2.Fill.SH_finite_ncard_le
import PrimePairNB.Paper2.M2.Fill.nearBad_finite_ncard_le
import PrimePairNB.Paper2.M2.Fill.pairSum_ne_zero_of_not_nearBad
import PrimePairNB.Paper2.M2.Fill.eventually_nearBad_small

/-! `prop_Lambda_core` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`prop_Lambda_proof` for `y > 0` and small `ε`** (Z1, Z2, Z4, Z5, Z6, `B < 1`). `A₀, t₀` from (Z4);
`thm_single_proof` gives `c₂`, `X₀`; `Y = y + 1`, `H₀` from `pairSum_ne_zero_of_not_nearBad`, `C` from
`SH_finite_ncard_le`. Given `N`, pick `X ≥ max(X₀, 3)` with `2 log X ≥ H₀` and
`N + |NearBad H Y| ≤ (c₂/2)X²/log² X`, `H = 2 log X`. The good pairs with `u = ρ/q ∉ NearBad H Y` number at least
`N`, and each gives a point `1 + u` of `LambdaSet y ε`. -/
theorem prop_Lambda_core (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1)
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) (hε1 : ε < 1) :
    (LambdaSet y ε).Infinite := by
  obtain ⟨A₀, hA₀, t₀, hN0⟩ := hZ4
  obtain ⟨c₂, hc₂, X₀, hX₀⟩ := thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy
  set Y : ℝ := y + 1 with hYdef
  have hY : 0 < Y := by linarith
  obtain ⟨H₀, hH₀⟩ := pairSum_ne_zero_of_not_nearBad hZ1 hZ2 hZ6 hB hY
  obtain ⟨C, hC, hSH⟩ := SH_finite_ncard_le hZ1 hZ2 hB
  apply infinite_of_forall_le_ncard
  intro N
  obtain ⟨X, hXbig, hXge, hXlog⟩ := ((eventually_nearBad_small hc₂ hC hY.le (N : ℝ)).and
    ((Filter.eventually_ge_atTop (max X₀ 3)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (H₀ / 2)))).exists
  have hX₀' : X₀ ≤ X := le_of_max_le_left hXge
  have hX3 : 3 ≤ X := le_of_max_le_right hXge
  obtain ⟨hfin, -, -, hgood, hb, hinj⟩ := hX₀ X hX₀' hX3
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set H : ℝ := 2 * Real.log X with hHdef
  have hH0 : 0 ≤ H := by positivity
  have hHH₀ : H₀ ≤ H := by linarith
  obtain ⟨hSHfin, hSHle⟩ := hSH (H + Y) (by linarith)
  obtain ⟨hNBfin, hNBle⟩ := nearBad_finite_ncard_le hZ1 hH0 hY.le hSHfin
  have hNBreal : ((NearBad H Y).ncard : ℝ) ≤ (C * (H + Y + 1) * Real.log (H + Y + 3)) ^ 2 := by
    have h1 : ((NearBad H Y).ncard : ℝ) ≤ ((SH (H + Y)).ncard : ℝ) ^ 2 := by exact_mod_cast hNBle
    exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hSHle 2)
  -- the good pairs, split by near-badness
  set G := {p : ℂ × ℕ | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2} with hG
  set T := {p : ℂ × ℕ | p.1 / (p.2 : ℂ) ∈ NearBad H Y} with hT
  have hGsub : G ⊆ singlePairs A₀ y ε X := fun p hp => hp.1
  have hGfin : G.Finite := hfin.subset hGsub
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard G T hGfin
  have hbad : (G ∩ T).ncard ≤ (NearBad H Y).ncard :=
    Set.ncard_le_ncard_of_injOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (fun p hp => hp.2)
      (hinj.mono fun p hp => hGsub hp.1) hNBfin
  have hcount : (N : ℝ) ≤ ((G \ T).ncard : ℝ) := by
    have e : ((G ∩ T).ncard : ℝ) + ((G \ T).ncard : ℝ) = (G.ncard : ℝ) := by exact_mod_cast hsplit
    have hbad' : ((G ∩ T).ncard : ℝ) ≤ ((NearBad H Y).ncard : ℝ) := by exact_mod_cast hbad
    linarith
  -- the points `1 + u`
  have hinj' : InjOn (fun p : ℂ × ℕ => 1 + p.1 / (p.2 : ℂ)) (G \ T) := by
    intro p hp p' hp' h
    exact hinj (hGsub hp.1) (hGsub hp'.1) (add_left_cancel h)
  refine ⟨(fun p : ℂ × ℕ => 1 + p.1 / (p.2 : ℂ)) '' (G \ T), ?_, (hGfin.sdiff).image _, ?_⟩
  · rintro _ ⟨p, ⟨⟨hsp, hs⟩, hnT⟩, rfl⟩
    obtain ⟨hdist, hreu, -, -, hnorm, hlow⟩ := hb p hsp hs
    obtain ⟨hρ, hre, -, -, hq, -⟩ := hsp
    set u : ℂ := p.1 / (p.2 : ℂ) with hu
    refine ⟨p.1, hρ, hre, p.2, hq, rfl, ?_, ?_⟩
    · rw [mem_ball, Complex.dist_eq]
      convert hdist using 2
      ring
    · have huQ : u ∈ PoleSetQ := Or.inr ⟨p.2, hq.one_lt.le, hq.squarefree, p.1, hρ, rfl⟩
      have hq2 : (2 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hq.two_le
      have hre0 : 0 < u.re := by rw [hreu]; positivity
      have hre1 : u.re ≤ 1 := by
        rw [hreu, div_le_one (by positivity)]; linarith
      have hu1 : u ≠ 1 := by
        intro h1
        have : u.re = 1 := by rw [h1, one_re]
        rw [hreu, div_eq_one_iff_eq (by positivity)] at this
        linarith
      have hYu : |u.im| ≤ Y := by
        have him : |(u - (y : ℂ) * I).im| ≤ ‖u - (y : ℂ) * I‖ := Complex.abs_im_le_norm _
        have e : (u - (y : ℂ) * I).im = u.im - y := by simp
        rw [e] at him
        have := lt_of_le_of_lt him hdist
        rw [abs_lt] at this
        rw [abs_le]
        constructor <;> linarith
      have hexp : Real.exp (-H) < ‖2 * Rcoef u / u‖ := by
        have hX0 : 0 < X := by linarith
        have e1 : Real.exp (-H) = (X ^ 2)⁻¹ := by
          rw [hHdef, show -(2 * Real.log X) = Real.log ((X ^ 2)⁻¹) by
            rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
        have e2 : (X ^ 2)⁻¹ < 2 / (X + 1) := by
          rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        rw [e1, hnorm]
        exact lt_of_lt_of_le e2 hlow
      exact hH₀ H hHH₀ u huQ hu1 hre0 hre1 hYu hnT hexp
  · rw [hinj'.ncard_image]
    exact_mod_cast hcount

end GoldbachBoundaries.Paper2.M2
