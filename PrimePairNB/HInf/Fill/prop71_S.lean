import PrimePairNB.HInf.Fill.bracketK_ne_zero
import PrimePairNB.HInf.Fill.pairSumS_ne_zero_of_not_nearBad

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2
namespace GoldbachBoundaries.HInf.Fill

lemma continuousAt_KS_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : ContinuousAt KS w := by
  have hG (z : ℂ) (hz : z.im ≠ 0) : ContinuousAt Gamma z := by
    apply Complex.continuousAt_Gamma
    intro n he
    apply hz
    simp [he]
  exact (hG w hw).mul ((hG (2 - w) (by simpa using hw)).comp (by fun_prop))

lemma bracketK_lower {y ε : ℝ} (hε : 0 < ε) (hεy : ε < y) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ closedBall ((y : ℂ) * I) ε,
      κ ≤ ‖KS (1 - u / 4) + KS (1 / 2 + u / 4)‖ := by
  have him (u : ℂ) (hu : u ∈ closedBall ((y : ℂ) * I) ε) : u.im ≠ 0 := by
    have hn : ‖u - (y : ℂ) * I‖ ≤ ε := by simpa [mem_closedBall, dist_eq_norm] using hu
    have hh := (Complex.abs_im_le_norm (u - (y : ℂ) * I)).trans hn
    have hh' : |u.im - y| ≤ ε := by simpa using hh
    have := (abs_le.mp hh').1
    linarith
  have hcont : ContinuousOn (fun u : ℂ => ‖KS (1 - u / 4) + KS (1 / 2 + u / 4)‖)
      (closedBall ((y : ℂ) * I) ε) := by
    intro u hu
    have hi := him u hu
    have h1 : (1 - u / 4).im ≠ 0 := by simpa using neg_ne_zero.mpr (div_ne_zero hi (by norm_num : (4 : ℝ) ≠ 0))
    have h2 : (1 / 2 + u / 4).im ≠ 0 := by simpa using div_ne_zero hi (by norm_num : (4 : ℝ) ≠ 0)
    have hc1 : ContinuousAt (fun z : ℂ => KS (1 - z / 4)) u :=
      ContinuousAt.comp (g := KS) (f := fun z : ℂ => 1 - z / 4) (continuousAt_KS_of_im_ne_zero h1) (by fun_prop)
    have hc2 : ContinuousAt (fun z : ℂ => KS (1 / 2 + z / 4)) u :=
      ContinuousAt.comp (g := KS) (f := fun z : ℂ => 1 / 2 + z / 4) (continuousAt_KS_of_im_ne_zero h2) (by fun_prop)
    exact (hc1.add hc2).norm.continuousWithinAt
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall ((y : ℂ) * I) ε).exists_isMinOn
    (nonempty_closedBall.mpr hε.le) hcont
  exact ⟨_, norm_pos_iff.mpr (bracketK_ne_zero (him u hu)), hmin⟩

/-- Single representations are retained for the joint conclusion. -/
def arithPoints (T : ℂ → Prop) (y ε : ℝ) : Set ℂ :=
  {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
    IsSingleRep ρ q ∧ s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ T s₀}

set_option maxHeartbeats 1000000 in
/-- The common counting argument, with the two independent main-term bounds. -/
lemma prop71_arith_core (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hB : Bsup < 1)
    (T : ℂ → Prop)
    (hT : ∀ Y : ℝ, 0 < Y → ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      ∀ u ∈ PoleSetQ, u ≠ 1 → 0 < u.re → u.re ≤ 1 → |u.im| ≤ Y → u ∉ NearBad H Y →
      Real.exp (-H) < ‖2 * Rcoef u / u‖ →
      Real.exp (-H) < ‖Rcoef u * (KS (1 - u / 4) + KS (1 / 2 + u / 4))‖ → T (1 + u))
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) (hε1 : ε < 1) :
    (arithPoints T y ε).Infinite := by
  obtain ⟨A₀, hA₀, t₀, hN0⟩ := hZ4
  obtain ⟨c₂, hc₂, X₀, hX₀⟩ := thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy
  set Y : ℝ := y + 1 with hYdef
  have hY : 0 < Y := by linarith
  obtain ⟨H₀, hH₀⟩ := hT Y hY
  obtain ⟨C, hC, hSH⟩ := SH_finite_ncard_le hZ1 hZ2 hB
  obtain ⟨κ, hκ, hκbound⟩ := bracketK_lower hε hεy
  let c := κ * (y - ε)
  have hc : 0 < c := mul_pos hκ (sub_pos.mpr hεy)
  apply infinite_of_forall_le_ncard
  intro N
  obtain ⟨X, hXbig, hXge, hXlog⟩ := ((eventually_nearBad_small hc₂ hC hY.le (N : ℝ)).and
    ((Filter.eventually_ge_atTop (max (max X₀ 3) (2 / c + 3))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (H₀ / 2)))).exists
  have hX₀' : X₀ ≤ X := (le_max_left X₀ 3).trans ((le_max_left _ _).trans hXge)
  have hX3 : 3 ≤ X := (le_max_right X₀ 3).trans ((le_max_left _ _).trans hXge)
  have hXc : 2 / c + 3 ≤ X := (le_max_right _ _).trans hXge
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
    refine ⟨p.1, hρ, hre, p.2, hq, rfl, hs, ?_, ?_⟩
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
      have hexpS : Real.exp (-H) < ‖Rcoef u * (KS (1 - u / 4) + KS (1 / 2 + u / 4))‖ := by
        have hX0 : 0 < X := by linarith
        have e1 : Real.exp (-H) = (X ^ 2)⁻¹ := by
          rw [hHdef, show -(2 * Real.log X) = Real.log ((X ^ 2)⁻¹) by
            rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
        have hXmul : 2 < c * X := by
          have hh := (div_le_iff₀ hc).mp (show 2 / c ≤ X - 3 by linarith)
          nlinarith
        have e2 : (X ^ 2)⁻¹ < c / (X + 1) := by
          rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have huNorm : y - ε ≤ ‖u‖ := by
          have hi := (Complex.abs_im_le_norm (u - (y : ℂ) * I)).trans hdist.le
          have hi' : |u.im - y| ≤ ε := by simpa using hi
          have hh := (abs_le.mp hi').1
          linarith [Complex.im_le_norm u]
        have hu0 : 0 < ‖u‖ := lt_of_lt_of_le (sub_pos.mpr hεy) huNorm
        have hR : ‖u‖ / (X + 1) ≤ ‖Rcoef u‖ := by
          have hh : 2 / (X + 1) ≤ 2 * ‖Rcoef u‖ / ‖u‖ := by
            rw [← hnorm, norm_div, norm_mul, norm_ofNat] at hlow
            exact hlow
          have hh' := (le_div_iff₀ hu0).mp hh
          rw [div_mul_eq_mul_div] at hh'
          have hh'' := (div_le_iff₀ (by positivity : 0 < X + 1)).mp hh'
          apply (div_le_iff₀ (by positivity : 0 < X + 1)).mpr
          linarith only [hh'']
        have hbκ := hκbound u (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hdist.le))
        rw [e1, norm_mul]
        calc
          (X ^ 2)⁻¹ < c / (X + 1) := e2
          _ = ((y - ε) / (X + 1)) * κ := by dsimp [c]; ring
          _ ≤ (‖u‖ / (X + 1)) * κ := by gcongr
          _ ≤ ‖Rcoef u‖ * ‖KS (1 - u / 4) + KS (1 / 2 + u / 4)‖ := by gcongr
      exact hH₀ H hHH₀ u huQ hu1 hre0 hre1 hYu hnT hexp hexpS
  · rw [hinj'.ncard_image]
    exact_mod_cast hcount

lemma pairSumS_conj (hZ1 : Z1) (s : ℂ) : pairSumS (conj s) = conj (pairSumS s) := by
  unfold pairSumS
  rw [← (M2.FillF.pinchPairsConj s).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun p => ?_
  have ha := Rcoef_real_conj hZ1 p.2.1
  have hb := Rcoef_real_conj hZ1 p.2.2.1
  have hra : conj (Rcoef p.1.1) = Rcoef p.1.1 := Complex.conj_eq_iff_im.mpr ha.1
  have hrb : conj (Rcoef p.1.2) = Rcoef p.1.2 := Complex.conj_eq_iff_im.mpr hb.1
  change Rcoef (conj p.1.1) * Rcoef (conj p.1.2) *
    KS ((conj p.1.1 - conj p.1.2 + 3) / 4) = _
  rw [ha.2, hb.2]
  simp only [KS, map_mul, hra, hrb, ← Complex.Gamma_conj, map_sub, map_add, map_div₀, map_ofNat]

private lemma arithPoints_mono_radius {T : ℂ → Prop} {y ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    arithPoints T y ε₁ ⊆ arithPoints T y ε₂ := by
  rintro s ⟨ρ, hρ, hre, q, hq, rfl, hs, hball, hne⟩
  exact ⟨ρ, hρ, hre, q, hq, rfl, hs, Metric.ball_subset_ball h hball, hne⟩

private lemma conj_mem_arithPoints {T : ℂ → Prop} (hT : ∀ s, T s → T (conj s))
    {y ε : ℝ} {s : ℂ} (h : s ∈ arithPoints T (-y) ε) : conj s ∈ arithPoints T y ε := by
  obtain ⟨ρ, hρ, hre, q, hq, rfl, hs, hball, hne⟩ := h
  refine ⟨conj ρ, conj_mem_nontrivialZeros hρ, by simpa using hre, q, hq, by simp, ?_, ?_, ?_⟩
  · rintro ρ' k ⟨hρ', hk, hsq, heq⟩
    have hrep : IsRep (ρ / (q : ℂ)) (conj ρ') k := by
      refine ⟨conj_mem_nontrivialZeros hρ', hk, hsq, ?_⟩
      have := congrArg conj heq
      simpa using this
    obtain ⟨h1, h2⟩ := hs (conj ρ') k hrep
    refine ⟨?_, h2⟩
    rw [← h1, Complex.conj_conj]
  · have hc : (1 : ℂ) + (y : ℂ) * I = conj (1 + ((-y : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [mem_ball, hc, Complex.dist_conj_conj]
    exact hball
  · simpa using hT _ hne

lemma prop71_arith_of_core (T : ℂ → Prop) (hT : ∀ s, T s → T (conj s))
    (hcore : ∀ y ε : ℝ, 0 < y → 0 < ε → ε < y → ε < 1 → (arithPoints T y ε).Infinite) (y ε : ℝ) (hε : 0 < ε) :
    (arithPoints T y ε).Infinite := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · -- `y < 0`: conjugate from `-y`.
    set ε' := min ε (min (-y / 2) (1 / 2)) with hε'
    have h0 : 0 < ε' := lt_min hε (lt_min (by linarith) (by norm_num))
    have h1 : ε' < -y := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have h2 : ε' < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    have hinf := hcore (-y) ε' (by linarith) h0 h1 h2
    have himg : (conj '' arithPoints T (-y) ε').Infinite :=
      hinf.image (star_injective.injOn)
    refine himg.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s ∈ arithPoints T (-y) ε := arithPoints_mono_radius (min_le_left _ _) hs
    exact conj_mem_arithPoints hT hs'
  · -- `y = 0`: points near `1 + iε/2`.
    set ε₃ := min (ε / 4) (1 / 2) with hε₃
    have h0 : 0 < ε₃ := lt_min (by linarith) (by norm_num)
    have h1 : ε₃ < ε / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h2 : ε₃ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine (hcore (ε / 2) ε₃ (by linarith) h0 h1 h2).mono ?_
    rintro s ⟨ρ, hρ, hre, q, hq, rfl, hs, hball, hne⟩
    refine ⟨ρ, hρ, hre, q, hq, rfl, hs, ?_, hne⟩
    refine Metric.ball_subset_ball' ?_ hball
    have hd : dist (1 + ((ε / 2 : ℝ) : ℂ) * I) (1 + ((0 : ℝ) : ℂ) * I) = ε / 2 := by
      rw [Complex.dist_eq]
      simp only [ofReal_zero, zero_mul, add_zero, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    rw [hd]
    linarith [min_le_left (ε / 4) (1 / 2)]
  · -- `y > 0`: shrink the radius.
    set ε' := min ε (min (y / 2) (1 / 2)) with hε'
    have h0 : 0 < ε' := lt_min hε (lt_min (by linarith) (by norm_num))
    have h1 : ε' < y := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have h2 : ε' < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    exact (hcore y ε' hy h0 h1 h2).mono (arithPoints_mono_radius (min_le_left _ _))

theorem prop71_S (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSumS s₀ ≠ 0}.Infinite := by
  have hcore : ∀ y ε : ℝ, 0 < y → 0 < ε → ε < y → ε < 1 →
      (arithPoints (fun s => pairSumS s ≠ 0) y ε).Infinite := by
    intro y ε hy hε hεy hε1
    apply prop71_arith_core hZ1 hZ2 hZ4 hZ5 hB (fun s => pairSumS s ≠ 0) ?_ hy hε hεy hε1
    intro Y hY
    obtain ⟨H₀, hH₀⟩ := pairSumS_ne_zero_of_not_nearBad hZ1 hZ2 hB hY
    exact ⟨H₀, fun H hH u hu hu1 hre hre1 hYu hnB _ heS =>
      hH₀ H hH u hu hu1 hre hre1 hYu hnB heS⟩
  refine (prop71_arith_of_core (fun s => pairSumS s ≠ 0) ?_ hcore y ε hε).mono ?_
  · intro s hs
    rw [pairSumS_conj hZ1]
    exact (map_ne_zero _).mpr hs
  · rintro s ⟨ρ, hρ, hre, q, hq, heq, _, hball, hne⟩
    exact ⟨ρ, hρ, hre, q, hq, heq, hball, hne⟩

end GoldbachBoundaries.HInf.Fill
