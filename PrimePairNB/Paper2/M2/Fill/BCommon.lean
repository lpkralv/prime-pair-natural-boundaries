import PrimePairNB.Paper2.M2.Rigidity

/-! Shared helpers (zero and prime counts) for `Single.lean`.

Proofs of the counting lemmas of `Single.lean`, so that the files `Fill/<L>.lean` can cite each other's
content:

* `ncard_zeros_le_NzeroB`: distinct zeros with `0 < γ ≤ t` versus `N(t)`.
* `Nzero_le_mul_logB`: `N(t) ≤ t log t` for large `t` (Z2).
* facts on `M(X) = ⌈2 log X/A₀⌉₊`: `2 log X/A₀ ≤ M`, eventually `M ≤ 3 log X/A₀`, `X/M → ∞`.
* `ncard_lineZeros_window_geB`, `ncard_primes_window_geB`: the zero and prime counts.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Zero counts -/

lemma ncard_zeros_le_NzeroB (t : ℝ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}.Finite ∧
      ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}.ncard : ℝ) ≤ Nzero t := by
  have hfin := finite_zeros_im_pos_le t
  refine ⟨hfin, ?_⟩
  unfold Nzero
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  exact_mod_cast one_le_zetaMult hρ.1

lemma Nzero_le_mul_logB (hZ2 : Z2) : ∀ᶠ t in atTop, Nzero t ≤ t * Real.log t := by
  obtain ⟨C, hC⟩ := hZ2.1
  filter_upwards [hC, eventually_ge_atTop (2 * Real.pi), eventually_ge_atTop (2 * |C|)] with t ht h2π hCt
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have htpos : 0 < t := by linarith
  have h1t : 1 ≤ t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg h1t
  have hdiv : 1 ≤ t / (2 * Real.pi) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hlogle : Real.log (t / (2 * Real.pi)) ≤ Real.log t := by
    apply Real.log_le_log (by linarith)
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hup := (abs_le.mp ht).2
  -- `N(t) ≤ (t/2π) log t - t/2π + C log t`
  have h1 : t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ≤ t / (2 * Real.pi) * Real.log t :=
    mul_le_mul_of_nonneg_left hlogle (by positivity)
  have h2 : C * Real.log t ≤ t / 2 * Real.log t := by
    have : C ≤ t / 2 := by have := le_abs_self C; linarith
    exact mul_le_mul_of_nonneg_right this hlog0
  have h3 : t / (2 * Real.pi) ≤ t / 2 := by
    apply div_le_div_of_nonneg_left htpos.le (by norm_num); linarith
  have h4 : t / (2 * Real.pi) * Real.log t ≤ t / 2 * Real.log t :=
    mul_le_mul_of_nonneg_right h3 hlog0
  have h5 : 0 ≤ t / (2 * Real.pi) := by positivity
  nlinarith

/-! ## `M(X)` -/

lemma Mfun_ge {A₀ X : ℝ} : 2 * Real.log X / A₀ ≤ (Mfun A₀ X : ℝ) := Nat.le_ceil _

lemma Mfun_pos {A₀ X : ℝ} (hA₀ : 0 < A₀) (hX : 1 < X) : 0 < (Mfun A₀ X : ℝ) :=
  lt_of_lt_of_le (by have := Real.log_pos hX; positivity) Mfun_ge

lemma eventually_Mfun_le {A₀ : ℝ} (hA₀ : 0 < A₀) :
    ∀ᶠ X in atTop, (Mfun A₀ X : ℝ) ≤ 3 * Real.log X / A₀ := by
  filter_upwards [eventually_ge_atTop (Real.exp A₀), eventually_gt_atTop 1] with X hX hX1
  have hlog : A₀ ≤ Real.log X := by
    rw [← Real.log_exp A₀]; exact Real.log_le_log (Real.exp_pos _) hX
  have hlt := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log X / A₀ by
    have := Real.log_pos hX1; positivity)
  unfold Mfun
  have : 2 * Real.log X / A₀ + 1 ≤ 3 * Real.log X / A₀ := by
    rw [div_add_one hA₀.ne', div_le_div_iff_of_pos_right hA₀]; linarith
  linarith

lemma tendsto_div_Mfun {A₀ : ℝ} (hA₀ : 0 < A₀) :
    Tendsto (fun X : ℝ => X / (Mfun A₀ X : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  set δ : ℝ := A₀ / (3 * (|b| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hlo := (Real.isLittleO_log_id_atTop).bound hδpos
  filter_upwards [hlo, eventually_Mfun_le hA₀, eventually_gt_atTop 1] with X hlogX hM hX1
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hXpos : 0 < X := by linarith
  rw [Real.norm_of_nonneg hlog.le, id, Real.norm_of_nonneg hXpos.le] at hlogX
  have hMpos := Mfun_pos hA₀ hX1
  -- `X/M ≥ A₀ X/(3 log X) ≥ A₀/(3δ) = |b| + 1`
  have h1 : A₀ * X / (3 * Real.log X) ≤ X / (Mfun A₀ X : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hMpos]
    have := mul_le_mul_of_nonneg_left hM (show 0 ≤ X * A₀ by positivity)
    calc A₀ * X * (Mfun A₀ X : ℝ) = X * A₀ * (Mfun A₀ X : ℝ) := by ring
      _ ≤ X * A₀ * (3 * Real.log X / A₀) := this
      _ = X * (3 * Real.log X) := by field_simp
  have h2 : |b| + 1 ≤ A₀ * X / (3 * Real.log X) := by
    rw [le_div_iff₀ (by positivity)]
    have : (|b| + 1) * (3 * δ) = A₀ := by rw [hδ]; field_simp
    nlinarith [abs_nonneg b]
  linarith [le_abs_self b]

/-! ## Zeros on the line in `(X/M, X]` -/

lemma ncard_lineZeros_window_geB (hZ2 : Z2) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) :
    ∀ᶠ X in atTop,
      {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < ρ.im ∧ ρ.im ≤ X}.Finite ∧
      A₀ / 2 * X ≤
        ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < ρ.im ∧ ρ.im ≤ X}.ncard : ℝ) := by
  have hNz := (tendsto_div_Mfun hA₀).eventually (Nzero_le_mul_logB hZ2)
  filter_upwards [hNz, eventually_ge_atTop t₀, eventually_gt_atTop 1] with X hNzX hXt₀ hX1
  set M : ℝ := (Mfun A₀ X : ℝ) with hMdef
  have hMpos : 0 < M := Mfun_pos hA₀ hX1
  have hM1 : 1 ≤ M := by
    have : 0 < Mfun A₀ X := Nat.cast_pos.mp hMpos
    rw [hMdef]; exact_mod_cast this
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < X / M := div_pos hXpos hMpos
  have hYle : X / M ≤ X := div_le_self hXpos.le hM1
  set L : ℝ → Set ℂ := fun t => {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im ∧ ρ.im ≤ t}
    with hLdef
  have hLfin : ∀ t, (L t).Finite := fun t =>
    (finite_zeros_im_pos_le t).subset fun ρ ⟨hρ, _, h0, ht⟩ => ⟨hρ, h0, ht⟩
  have hsub : L (X / M) ⊆ L X := fun ρ ⟨hρ, hre, h0, ht⟩ => ⟨hρ, hre, h0, ht.trans hYle⟩
  have hW : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / M < ρ.im ∧ ρ.im ≤ X} = L X \ L (X / M) := by
    ext ρ
    constructor
    · rintro ⟨hρ, hre, h1, h2⟩
      exact ⟨⟨hρ, hre, hYpos.trans h1, h2⟩, fun ⟨_, _, _, h⟩ => absurd h (not_le.mpr h1)⟩
    · rintro ⟨⟨hρ, hre, h0, h2⟩, h⟩
      exact ⟨hρ, hre, lt_of_not_ge fun hle => h ⟨hρ, hre, h0, hle⟩, h2⟩
  rw [hW]
  refine ⟨(hLfin X).sdiff, ?_⟩
  rw [Set.ncard_sdiff hsub (hLfin _), Nat.cast_sub (Set.ncard_le_ncard hsub (hLfin X))]
  have hN0X : A₀ * X ≤ ((L X).ncard : ℝ) := hN0 X hXt₀
  -- `N₀(X/M) ≤ N(X/M) ≤ (X/M) log(X/M) ≤ (X/M) log X ≤ A₀X/2`
  have hc1 : ((L (X / M)).ncard : ℝ) ≤
      ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ X / M}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard
      (show L (X / M) ⊆ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ X / M} from
        fun ρ ⟨hρ, _, h0, ht⟩ => ⟨hρ, h0, ht⟩) (finite_zeros_im_pos_le _)
  have hc2 := (ncard_zeros_le_NzeroB (X / M)).2
  have hc3 : X / M * Real.log (X / M) ≤ X / M * Real.log X :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hYpos hYle) hYpos.le
  have hc4 : X / M * Real.log X ≤ A₀ / 2 * X := by
    have hge : 2 * Real.log X / A₀ ≤ M := Mfun_ge
    have hlogM : Real.log X ≤ A₀ * M / 2 := by
      rw [div_le_iff₀ hA₀] at hge; linarith
    calc X / M * Real.log X ≤ X / M * (A₀ * M / 2) := mul_le_mul_of_nonneg_left hlogM hYpos.le
      _ = A₀ / 2 * X := by field_simp
  linarith

/-! ## Primes in a window -/

lemma ncard_primes_window_geB (hZ5 : Z5) {A₀ y ε : ℝ} (hA₀ : 0 < A₀) (hy : 0 < y) (hε : 0 < ε)
    (hεy : ε < y) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ X in atTop, ∀ γ : ℝ, X / (Mfun A₀ X : ℝ) < γ → γ ≤ X →
      {q : ℕ | q.Prime ∧ γ / (q : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}.Finite ∧
      c₁ * X / Real.log X ^ 2 ≤
        ({q : ℕ | q.Prime ∧ γ / (q : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}.ncard : ℝ) := by
  set a := y - ε / 2 with ha
  set b := y + ε / 2 with hb
  have hapos : 0 < a := by rw [ha]; linarith
  have hbpos : 0 < b := by rw [hb]; linarith
  set θ := ε / a with hθ
  have hθpos : 0 < θ := div_pos hε hapos
  have h1θ : 1 + θ = b / a := by
    rw [hθ, eq_div_iff hapos.ne', add_mul, one_mul, div_mul_cancel₀ _ hapos.ne', ha, hb]; ring
  obtain ⟨x₀, hx₀⟩ := hZ5 θ hθpos
  refine ⟨θ * A₀ / (12 * b), by positivity, ?_⟩
  have hT := (tendsto_div_Mfun hA₀).eventually (eventually_ge_atTop (b * max x₀ 2))
  filter_upwards [hT, eventually_Mfun_le hA₀, eventually_gt_atTop 1, eventually_ge_atTop (1 / b)]
    with X hXM hMle hX1 hXb γ hγ1 hγ2
  set M : ℝ := (Mfun A₀ X : ℝ) with hMdef
  have hMpos : 0 < M := Mfun_pos hA₀ hX1
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hγpos : 0 < γ := lt_of_le_of_lt (div_pos hXpos hMpos).le hγ1
  set x := γ / b with hx
  have hxa : (1 + θ) * x = γ / a := by
    rw [h1θ, hx]; field_simp
  -- the set is the (Z5) set at `(θ, x)`
  have hset : {q : ℕ | q.Prime ∧ γ / (q : ℝ) ∈ Ioo a b} =
      {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < (1 + θ) * x} := by
    ext q
    simp only [mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨hq, h1, h2⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      refine ⟨hq, ?_, ?_⟩
      · rw [hx, div_lt_iff₀ hbpos]; rw [div_lt_iff₀ hq0] at h2; linarith
      · rw [hxa, lt_div_iff₀ hapos]; rw [lt_div_iff₀ hq0] at h1; linarith
    · rintro ⟨hq, h1, h2⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      refine ⟨hq, ?_, ?_⟩
      · rw [lt_div_iff₀ hq0]; rw [hxa, lt_div_iff₀ hapos] at h2; linarith
      · rw [div_lt_iff₀ hq0]; rw [hx, div_lt_iff₀ hbpos] at h1; linarith
  rw [hset]
  refine ⟨?_, ?_⟩
  · refine (Set.finite_Iio ⌈(1 + θ) * x⌉₊).subset fun p ⟨_, _, h2⟩ => ?_
    simp only [mem_Iio]
    exact_mod_cast h2.trans_le (Nat.le_ceil _)
  -- `x ≥ X/(Mb) ≥ max x₀ 2`
  have hxlow : X / M / b < x := by rw [hx]; exact div_lt_div_of_pos_right hγ1 hbpos
  have hxge : max x₀ 2 ≤ x := by
    have : max x₀ 2 ≤ X / M / b := by rw [le_div_iff₀ hbpos]; linarith
    linarith
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hxge
  have hxpos : 0 < x := by linarith
  have hcount := hx₀ x (le_trans (le_max_left _ _) hxge)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  -- `log x ≤ 2 log X` as `x ≤ X/b ≤ X²`
  have hxX2 : x ≤ X ^ 2 := by
    have h1 : x ≤ X / b := by rw [hx]; exact div_le_div_of_nonneg_right hγ2 hbpos.le
    have h2 : X / b ≤ X ^ 2 := by
      rw [div_le_iff₀ hbpos, sq]
      have : 1 ≤ X * b := by rw [div_le_iff₀ hbpos] at hXb; linarith
      nlinarith
    linarith
  have hlogle : Real.log x ≤ 2 * Real.log X := by
    have hl : Real.log (X ^ 2) = 2 * Real.log X := by rw [Real.log_pow]; norm_num
    rw [← hl]
    exact Real.log_le_log hxpos hxX2
  -- `θx/(2 log x) ≥ θx/(4 log X) ≥ θA₀X/(12 b log² X)`
  have hs1 : θ * x / (4 * Real.log X) ≤ θ * x / (2 * Real.log x) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
  have hxlow' : A₀ * X / (3 * b * Real.log X) ≤ x := by
    have hMb : M * b ≤ 3 * Real.log X / A₀ * b := mul_le_mul_of_nonneg_right hMle hbpos.le
    have : X / (3 * Real.log X / A₀ * b) ≤ X / (M * b) :=
      div_le_div_of_nonneg_left hXpos.le (by positivity) hMb
    have heq : X / (3 * Real.log X / A₀ * b) = A₀ * X / (3 * b * Real.log X) := by
      field_simp
    rw [div_div] at hxlow
    linarith
  have hs2 : θ * A₀ / (12 * b) * X / Real.log X ^ 2 ≤ θ * x / (4 * Real.log X) := by
    have : θ * A₀ / (12 * b) * X / Real.log X ^ 2 =
        θ * (A₀ * X / (3 * b * Real.log X)) / (4 * Real.log X) := by
      field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxlow' hθpos.le) (by positivity)
  linarith

/-! ## Real asymptotics -/

lemma eventually_four_mul_log_leB {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X in atTop, 4 * X * Real.log (2 * X) ≤ c / 2 * X ^ 2 / Real.log X ^ 2 := by
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound (show 0 < c / 16 by positivity)
  filter_upwards [hlo, eventually_ge_atTop 2] with X hX hX2
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (by positivity), id, Real.norm_of_nonneg hXpos.le] at hX
  -- `log(2X) ≤ 2 log X` as `2X ≤ X²`
  have hl2 : Real.log (2 * X) ≤ 2 * Real.log X := by
    have hl : Real.log (X ^ 2) = 2 * Real.log X := by rw [Real.log_pow]; norm_num
    rw [← hl]
    exact Real.log_le_log (by positivity) (by nlinarith)
  rw [le_div_iff₀ (by positivity)]
  have h1 : 4 * X * Real.log (2 * X) ≤ 4 * X * (2 * Real.log X) :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  calc 4 * X * Real.log (2 * X) * Real.log X ^ 2 ≤ 4 * X * (2 * Real.log X) * Real.log X ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 8 * X * Real.log X ^ 3 := by ring
    _ ≤ 8 * X * (c / 16 * X) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = c / 2 * X ^ 2 := by ring

/-! ## The count of `𝓟(X)` -/

lemma singlePairs_finite_ncard_geB (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ᶠ X in atTop, (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) := by
  classical
  obtain ⟨c₁, hc₁, hP⟩ := ncard_primes_window_geB hZ5 hA₀ hy hε hεy
  refine ⟨A₀ * c₁ / 2, by positivity, ?_⟩
  filter_upwards [ncard_lineZeros_window_geB hZ2 hA₀ hN0, hP, eventually_gt_atTop 1]
    with X hWX hPX hX1
  obtain ⟨hWfin, hWcard⟩ := hWX
  set W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < ρ.im ∧ ρ.im ≤ X}
    with hWdef
  set Q : ℂ → Set ℕ := fun ρ => {q : ℕ | q.Prime ∧ ρ.im / (q : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}
    with hQdef
  have hQfin : ∀ ρ ∈ W, (Q ρ).Finite := fun ρ hρ => (hPX ρ.im hρ.2.2.1 hρ.2.2.2).1
  have hQcard : ∀ ρ ∈ W, c₁ * X / Real.log X ^ 2 ≤ ((Q ρ).ncard : ℝ) :=
    fun ρ hρ => (hPX ρ.im hρ.2.2.1 hρ.2.2.2).2
  have hS : singlePairs A₀ y ε X = ⋃ ρ ∈ W, (fun q : ℕ => (ρ, q)) '' Q ρ := by
    ext ⟨ρ, q⟩
    simp only [singlePairs, mem_ofPred_eq, mem_iUnion, mem_image, Prod.mk.injEq, exists_prop]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨ρ, ⟨h1, h2, h3, h4⟩, q, ⟨h5, h6⟩, rfl, rfl⟩
    · rintro ⟨ρ', ⟨h1, h2, h3, h4⟩, q', ⟨h5, h6⟩, rfl, rfl⟩
      exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hSfin : (singlePairs A₀ y ε X).Finite := by
    rw [hS]; exact hWfin.biUnion fun ρ hρ => (hQfin ρ hρ).image _
  refine ⟨hSfin, ?_⟩
  -- fibres over the first coordinate
  have hmaps : Set.MapsTo Prod.fst (hSfin.toFinset : Set (ℂ × ℕ)) (hWfin.toFinset : Set ℂ) := by
    intro p hp
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hp ⊢
    rw [hS] at hp
    simp only [mem_iUnion, mem_image] at hp
    obtain ⟨ρ, hρ, q, _, rfl⟩ := hp
    exact hρ
  have hfib : ∀ ρ ∈ hWfin.toFinset,
      ({p ∈ hSfin.toFinset | p.1 = ρ}.card : ℝ) = ((Q ρ).ncard : ℝ) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hset : (({p ∈ hSfin.toFinset | p.1 = ρ} : Finset (ℂ × ℕ)) : Set (ℂ × ℕ)) =
        (fun q : ℕ => (ρ, q)) '' Q ρ := by
      ext ⟨ρ', q⟩
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, mem_ofPred_eq, mem_image,
        Prod.mk.injEq]
      rw [hS]
      simp only [mem_iUnion, mem_image, Prod.mk.injEq, exists_prop]
      constructor
      · rintro ⟨⟨i, _, x, hx, hi, hxq⟩, hρ'⟩
        subst hi hxq hρ'
        exact ⟨_, hx, rfl, rfl⟩
      · rintro ⟨x, hx, hρρ', hxq⟩
        subst hρρ' hxq
        exact ⟨⟨_, hρ, _, hx, rfl, rfl⟩, rfl⟩
    rw [← Set.ncard_coe_finset, hset, Set.ncard_image_of_injective _ (Prod.mk_right_injective ρ)]
  have hcardS : ((singlePairs A₀ y ε X).ncard : ℝ) =
      ∑ ρ ∈ hWfin.toFinset, ((Q ρ).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hSfin, Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    exact Finset.sum_congr rfl hfib
  have hlow : ∑ ρ ∈ hWfin.toFinset, c₁ * X / Real.log X ^ 2 ≤
      ∑ ρ ∈ hWfin.toFinset, ((Q ρ).ncard : ℝ) :=
    Finset.sum_le_sum fun ρ hρ => hQcard ρ ((Set.Finite.mem_toFinset _).mp hρ)
  rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hWfin] at hlow
  have hXpos : 0 < X := by linarith
  have hterm : 0 ≤ c₁ * X / Real.log X ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hWcard hterm
  have heq : A₀ * c₁ / 2 * X ^ 2 / Real.log X ^ 2 = A₀ / 2 * X * (c₁ * X / Real.log X ^ 2) := by ring
  rw [hcardS, heq]
  linarith

end GoldbachBoundaries.Paper2.M2
