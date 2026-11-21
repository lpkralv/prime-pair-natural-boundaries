import PrimePairNB.ThmA.G13_Continuation

/-!
# `exists_continuationAlong_of_uniform`

Proof: Lebesgue number `δ` for the cover of `[0,1]` by the preimages of the uniformity discs
`D_c = ball (γ c) (r c)`; subdivide `[0,1]` into `M` equal steps with `1/M < δ`, so that each grid
point `t_i = i/M` has a disc `D_i ⊇ γ (ball t_i δ)`. Inductively pick `F_i` analytic on `D_i`, in the
family at every point of `D_i`, with `F_{i+1} =ᶠ F_i` at `γ t_{i+1}`; neighbouring `F_i` agree on the
convex overlap `D_i ∩ D_{i+1}` (identity theorem). Put `f t = F_{k t}`, `k t = min ⌊tM⌋ (M-1)`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- **Existence of continuation for a uniform germ family.** If `B` is uniform on `U`
(`UniformFamily`), `γ` runs in `U` and `B (γ 0) f₀`, then `f₀` continues along `γ` with every germ in
the family.

Sketch. For each `t`, `UniformFamily` at `γ t` gives a radius `r_t`; by compactness of `[0,1]`
(Lebesgue number lemma, `lebesgue_number_lemma_of_metric` on the cover `γ ⁻¹' ball (γ t) (r_t/2)`)
pick `0 = t₀ < … < t_n = 1` and discs `D_i = ball p_i r_i` with `γ [t_i, t_{i+1}] ⊆ D_i`. Inductively
choose `F_i` analytic on `D_i` with `B` at every point of `D_i`, `F_0 =ᶠ f₀` at `γ 0`, and
`F_{i+1} =ᶠ F_i` at `γ t_{i+1}` (apply the uniform property at `p_{i+1}` with `q = γ t_{i+1}`, which
lies in `D_i ∩ D_{i+1}`). `F_i = F_{i+1}` on the convex `D_i ∩ D_{i+1}` (identity theorem). Put
`f t = F_i` for `t ∈ [t_i, t_{i+1})` (and `F_{n-1}` at `1`); `locallyEq` holds inside each piece
trivially and at each `t_i` because the two functions agree on the overlap. -/
theorem exists_continuationAlong_of_uniform {B : ℂ → (ℂ → ℂ) → Prop} {U : Set ℂ}
    (hB : UniformFamily B U) {γ : C(unitInterval, ℂ)} (hγ : ∀ t, γ t ∈ U) {f₀ : ℂ → ℂ}
    (h₀ : B (γ 0) f₀) :
    ∃ f : unitInterval → ℂ → ℂ, IsContinuationAlong γ f ∧ f 0 =ᶠ[𝓝 (γ 0)] f₀ ∧
      ∀ t, B (γ t) (f t) := by
  classical
  choose r hr hunif using fun c : unitInterval => hB (γ c) (hγ c)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set unitInterval))
    (c := fun c => γ ⁻¹' ball (γ c) (r c)) isCompact_univ
    (fun c => isOpen_ball.preimage γ.continuous)
    (fun t _ => mem_iUnion.mpr ⟨t, mem_ball_self (hr t)⟩)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  set M : ℝ := (N : ℝ) + 1 with hMdef
  have hM : 0 < M := by positivity
  -- grid points
  set tg : ℕ → unitInterval := fun i => projIcc 0 1 zero_le_one ((i : ℝ) / M) with htg
  choose c hc using fun i : ℕ => hleb (tg i) (mem_univ _)
  set D : ℕ → Set ℂ := fun i => ball (γ (c i)) (r (c i)) with hDdef
  have hDo : ∀ i, IsOpen (D i) := fun i => isOpen_ball
  have hmemD : ∀ i (s : unitInterval), dist s (tg i) < δ → γ s ∈ D i := fun i s hs =>
    hc i (mem_ball.mpr hs)
  have hstep : ∀ i, dist (tg (i + 1)) (tg i) < δ := by
    intro i
    rw [Subtype.dist_eq, Real.dist_eq]
    refine lt_of_le_of_lt (abs_projIcc_sub_projIcc _) ?_
    have : ((↑(i + 1) : ℝ) / M - (i : ℝ) / M) = 1 / M := by push_cast; field_simp; ring
    rw [this, abs_of_pos (by positivity)]
    exact hN
  have htg0 : tg 0 = 0 := by ext; simp [htg]
  -- the chain of discs and functions
  have hchain : ∀ n : ℕ, ∃ F : ℕ → ℂ → ℂ, F 0 =ᶠ[𝓝 (γ 0)] f₀ ∧
      (∀ i ≤ n, AnalyticOnNhd ℂ (F i) (D i) ∧ ∀ q ∈ D i, B q (F i)) ∧
      ∀ i < n, F (i + 1) =ᶠ[𝓝 (γ (tg (i + 1)))] F i := by
    intro n
    induction n with
    | zero =>
      have hq : γ 0 ∈ D 0 := by
        have := hmemD 0 (tg 0) (by rw [dist_self]; exact hδ)
        rwa [htg0] at this
      obtain ⟨F0, hFA, hFq, hFB⟩ := hunif (c 0) (γ 0) hq f₀ h₀
      refine ⟨fun _ => F0, hFq, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact ⟨hFA, hFB⟩
    | succ n ih =>
      obtain ⟨F, hF0, hFi, hFl⟩ := ih
      set q := γ (tg (n + 1))
      have hqn : q ∈ D n := hmemD n _ (hstep n)
      have hqn1 : q ∈ D (n + 1) := hmemD (n + 1) _ (by rw [dist_self]; exact hδ)
      obtain ⟨G, hGA, hGq, hGB⟩ :=
        hunif (c (n + 1)) q hqn1 (F n) ((hFi n le_rfl).2 q hqn)
      refine ⟨fun i => if i ≤ n then F i else G, ?_, fun i hi => ?_, fun i hi => ?_⟩
      · simpa using hF0
      · by_cases hin : i ≤ n
        · simp only [hin, ite_true]; exact hFi i hin
        · have : i = n + 1 := by omega
          subst this
          simp only [hin, ite_false]
          exact ⟨hGA, hGB⟩
      · by_cases hin : i < n
        · have h1 : i + 1 ≤ n := hin
          simp only [h1, hin.le, ite_true]
          exact hFl i hin
        · have : i = n := by omega
          subst this
          simp only [le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false]
          exact hGq
  obtain ⟨F, hF0, hFi, hFl⟩ := hchain N
  -- neighbouring functions agree on the overlaps
  have hov : ∀ i < N, EqOn (F (i + 1)) (F i) (D i ∩ D (i + 1)) := by
    intro i hi
    have hq : γ (tg (i + 1)) ∈ D i ∩ D (i + 1) :=
      ⟨hmemD i _ (hstep i), hmemD (i + 1) _ (by rw [dist_self]; exact hδ)⟩
    exact ((hFi (i + 1) hi).1.mono inter_subset_right).eqOn_of_preconnected_of_eventuallyEq
      ((hFi i hi.le).1.mono inter_subset_left)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hq (hFl i hi)
  have hadj : ∀ i j, i ≤ N → j ≤ N → j ≤ i + 1 → i ≤ j + 1 → ∀ z ∈ D i ∩ D j,
      F j =ᶠ[𝓝 z] F i := by
    intro i j hi hj h1 h2 z hz
    have hzo : D i ∩ D j ∈ 𝓝 z := ((hDo i).inter (hDo j)).mem_nhds hz
    rcases (show j = i ∨ j = i + 1 ∨ i = j + 1 by omega) with rfl | rfl | rfl
    · exact EventuallyEq.rfl
    · exact Filter.eventuallyEq_of_mem hzo (hov i (by omega))
    · exact (Filter.eventuallyEq_of_mem hzo
        (fun w hw => hov j (by omega) ⟨hw.2, hw.1⟩)).symm
  -- the index function
  set k : unitInterval → ℕ := fun s => min ⌊(s : ℝ) * M⌋₊ N with hkdef
  have hkN : ∀ s, k s ≤ N := fun s => min_le_right _ _
  have hkdist : ∀ s : unitInterval, dist s (tg (k s)) < δ := by
    intro s
    have hk1 : ((k s : ℕ) : ℝ) ≤ (s : ℝ) * M := by
      have : ((k s : ℕ) : ℝ) ≤ (⌊(s : ℝ) * M⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le (mul_nonneg s.2.1 hM.le))
    have hk2 : (s : ℝ) * M ≤ ((k s : ℕ) : ℝ) + 1 := by
      rcases min_choice ⌊(s : ℝ) * M⌋₊ N with h | h
      · have : k s = ⌊(s : ℝ) * M⌋₊ := h
        rw [this]; exact (Nat.lt_floor_add_one _).le
      · have : k s = N := h
        rw [this, ← hMdef]
        nlinarith [s.2.2]
    have hkM : ((k s : ℕ) : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hM, hMdef]
      have : ((k s : ℕ) : ℝ) ≤ N := by exact_mod_cast hkN s
      linarith
    have htk : ((tg (k s) : unitInterval) : ℝ) = ((k s : ℕ) : ℝ) / M := by
      simp only [htg]; rw [projIcc_of_mem _ hkM]
    rw [Subtype.dist_eq, Real.dist_eq, htk]
    have hlo : ((k s : ℕ) : ℝ) / M ≤ s := by rw [div_le_iff₀ hM]; exact hk1
    have hhi : (s : ℝ) - ((k s : ℕ) : ℝ) / M ≤ 1 / M := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hM]; linarith
    rw [abs_of_nonneg (by linarith)]
    exact lt_of_le_of_lt hhi hN
  have hkstep : ∀ s s' : unitInterval, dist s' s < 1 / M → k s' ≤ k s + 1 := by
    intro s s' hss
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt] at hss
    have h1 : (s' : ℝ) * M < (s : ℝ) * M + 1 := by
      have := hss.2; rw [lt_div_iff₀ hM] at this; nlinarith
    have h2 : ⌊(s' : ℝ) * M⌋₊ ≤ ⌊(s : ℝ) * M⌋₊ + 1 := by
      rw [← Nat.floor_add_one (mul_nonneg s.2.1 hM.le)]
      exact Nat.floor_mono h1.le
    simp only [hkdef]
    omega
  refine ⟨fun s => F (k s), ⟨fun s => ?_, fun s => ?_⟩, ?_, fun s => ?_⟩
  · exact (hFi (k s) (hkN s)).1 (γ s) (hmemD _ s (hkdist s))
  · have hev1 : ∀ᶠ s' in 𝓝 s, dist s' s < 1 / M := Metric.ball_mem_nhds s (by positivity)
    have hev2 : ∀ᶠ s' in 𝓝 s, γ s' ∈ D (k s) :=
      (γ.continuous.tendsto s).eventually ((hDo _).mem_nhds (hmemD _ s (hkdist s)))
    filter_upwards [hev1, hev2] with s' h1 h2
    have hs1 : s ∈ ball s' (1 / M) := by rw [mem_ball, dist_comm]; exact h1
    exact hadj (k s) (k s') (hkN s) (hkN s') (hkstep s s' h1)
      (hkstep s' s (mem_ball.mp hs1)) (γ s') ⟨h2, hmemD _ s' (hkdist s')⟩
  · have : k 0 = 0 := by simp [hkdef]
    simp only [this]; exact hF0
  · exact (hFi (k s) (hkN s)).2 (γ s) (hmemD _ s (hkdist s))

end GoldbachBoundaries.ThmA
