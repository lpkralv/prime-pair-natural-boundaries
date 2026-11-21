import PrimePairNB.ThmA.G20_Branches

/-!
# `exists_path_into`

Proof. Every `z ∈ U` has a ball `Δ(z, ε) ⊆ U` meeting `S` at most in `z` (`S` is discrete in `U`);
`Δ(z, ε) ∖ S` is the ball or the punctured ball, path connected in either case (the punctured ball
is the image of a half-plane under `w ↦ z + exp w`). The set `A` of `z ∈ U` having such a ball all
of whose points off `S` are joined to `a` inside `U ∖ S` is open, contains `a`, and satisfies
`closure A ∩ U ⊆ A`; as `U` is connected, `U ⊆ A`. Pick `b ∈ V ∖ S` (a point near any `v ∈ V`, other
than `v`) and take a path from `a` to `b`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

namespace PathIntoFill

/-- The punctured disc is path connected. -/
theorem isPathConnected_ball_diff_singleton (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (ball z ε \ {z}) := by
  have hH : IsPathConnected {w : ℂ | w.re < Real.log ε} :=
    (convex_halfSpace_re_lt (Real.log ε)).isPathConnected
      ⟨(Real.log ε - 1 : ℝ), by simp⟩
  have hcont : Continuous fun w : ℂ => z + Complex.exp w := by fun_prop
  have heq : (fun w : ℂ => z + Complex.exp w) '' {w : ℂ | w.re < Real.log ε} = ball z ε \ {z} := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
        calc Real.exp w.re < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr hw
          _ = ε := Real.exp_log hε
      · simp [Complex.exp_ne_zero]
    · rintro ⟨hu, hu'⟩
      have hne : u - z ≠ 0 := sub_ne_zero.mpr hu'
      refine ⟨Complex.log (u - z), ?_, ?_⟩
      · show (Complex.log (u - z)).re < Real.log ε
        rw [Complex.log_re]
        exact Real.log_lt_log (norm_pos_iff.mpr hne) (by rwa [mem_ball, dist_eq_norm] at hu)
      · simp only
        rw [Complex.exp_log hne]; ring
  rw [← heq]
  exact hH.image hcont

/-- A ball meeting `S` at most in its centre, minus `S`, is path connected. -/
theorem isPathConnected_ball_diff (S : Set ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ w ∈ ball z ε, w ≠ z → w ∉ S) : IsPathConnected (ball z ε \ S) := by
  by_cases hz : z ∈ S
  · have : ball z ε \ S = ball z ε \ {z} := by
      ext w
      constructor
      · rintro ⟨hw, hwS⟩
        exact ⟨hw, fun h => hwS (by rw [mem_singleton_iff.mp h]; exact hz)⟩
      · rintro ⟨hw, hwz⟩
        exact ⟨hw, hS w hw hwz⟩
    rw [this]; exact isPathConnected_ball_diff_singleton z hε
  · have : ball z ε \ S = ball z ε := by
      ext w
      refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
      by_cases hwz : w = z
      · rw [hwz]; exact hz
      · exact hS w hw hwz
    rw [this]; exact isPathConnected_ball hε

end PathIntoFill

open PathIntoFill in
/-- **Paths avoiding a discrete set** (general; the boundary theorem for `G` step 2, the domain corollary,
the every-path statement).

Sketch. `S ∩ U` has no accumulation point in `U` (`mem_codiscreteWithin`), so it is closed in `U`
and countable (a discrete subset of `ℂ`); `U ∖ S` is open. It is connected: `U` is open connected
and `S ∩ U` countable, and removing a countable closed set from a connected open subset of `ℝ²`
keeps it connected (local version of `Set.Countable.isPathConnected_compl_of_one_lt_rank`: cover by
balls, each ball minus a countable set is path connected). Then `IsOpen.isConnected_iff_isPathConnected`.
For `b`: `V` is open nonempty and `S ∩ V` is discrete, so `V ⊄ S`. -/
theorem exists_path_into {U S : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hS : ∀ᶠ z in codiscreteWithin U, z ∉ S) {a : ℂ} (ha : a ∈ U) (haS : a ∉ S) {V : Set ℂ}
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ b ∈ V, b ∉ S ∧ ∃ γ : C(unitInterval, ℂ), γ 0 = a ∧ γ 1 = b ∧ ∀ t, γ t ∈ U ∧ γ t ∉ S := by
  -- local structure: a ball inside `U` meeting `S` at most in the centre
  have hloc : ∀ z ∈ U, ∃ ε > 0, ball z ε ⊆ U ∧ ∀ w ∈ ball z ε, w ≠ z → w ∉ S := by
    intro z hz
    have h1 : {w | w ∉ S} ∪ Uᶜ ∈ 𝓝[≠] z :=
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hS) z hz
    have h2 : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU.mem_nhds hz)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem h1 h2)
    obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨min ε ε', lt_min hε hε', fun w hw => hε'U (ball_subset_ball (min_le_right _ _) hw),
      fun w hw hwz => ?_⟩
    have hw' : w ∈ ball z ε ∩ {z}ᶜ := ⟨ball_subset_ball (min_le_left _ _) hw, hwz⟩
    obtain ⟨h3 | h3, h4⟩ := hball hw'
    · exact h3
    · exact absurd h4 h3
  set A : Set ℂ := {z | ∃ ε > 0, ball z ε ⊆ U ∧ ∀ w ∈ ball z ε, w ∉ S → JoinedIn (U \ S) a w}
    with hAdef
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro z ⟨ε, hε, hεU, hεJ⟩
    refine ⟨ε, hε, fun z' hz' => ?_⟩
    have hd : 0 < ε - dist z' z := sub_pos.mpr (mem_ball.mp hz')
    have hsub : ball z' (ε - dist z' z) ⊆ ball z ε := by
      intro w hw
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle w z' z]
    exact ⟨ε - dist z' z, hd, hsub.trans hεU, fun w hw hwS => hεJ w (hsub hw) hwS⟩
  have haA : a ∈ A := by
    obtain ⟨ε, hε, hεU, hεS⟩ := hloc a ha
    refine ⟨ε, hε, hεU, fun w hw hwS => ?_⟩
    have hpc := isPathConnected_ball_diff S a hε hεS
    exact (hpc.joinedIn a ⟨mem_ball_self hε, haS⟩ w ⟨hw, hwS⟩).mono
      (fun u hu => ⟨hεU hu.1, hu.2⟩)
  have hclA : closure A ∩ U ⊆ A := by
    rintro z ⟨hzcl, hzU⟩
    obtain ⟨ε, hε, hεU, hεS⟩ := hloc z hzU
    obtain ⟨z', hz'b, hz'A⟩ := mem_closure_iff.mp hzcl (ball z ε) isOpen_ball (mem_ball_self hε)
    by_cases hzz : z' = z
    · rw [← hzz]; exact hz'A
    obtain ⟨ε', hε', -, hε'J⟩ := hz'A
    have hz'S : z' ∉ S := hεS z' hz'b hzz
    have hJ' : JoinedIn (U \ S) a z' := hε'J z' (mem_ball_self hε') hz'S
    have hpc := isPathConnected_ball_diff S z hε hεS
    refine ⟨ε, hε, hεU, fun w hw hwS => ?_⟩
    exact hJ'.trans ((hpc.joinedIn z' ⟨hz'b, hz'S⟩ w ⟨hw, hwS⟩).mono
      (fun u hu => ⟨hεU hu.1, hu.2⟩))
  have hUA : U ⊆ A := hUc.isPreconnected.subset_of_closure_inter_subset hAo ⟨a, ha, haA⟩ hclA
  -- a point of `V` off `S`
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨ε, hε, -, hεS⟩ := hloc v (hVU hv)
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV v hv
  set η : ℝ := min ε ρ / 2 with hηdef
  have hη : 0 < η := by positivity
  have hηlt : η < min ε ρ := by rw [hηdef]; linarith [lt_min hε hρ]
  set b : ℂ := v + (η : ℂ) with hbdef
  have hbd : dist b v = η := by
    rw [hbdef, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη]
  have hbV : b ∈ V := hρV (by rw [mem_ball, hbd]; exact lt_of_lt_of_le hηlt (min_le_right _ _))
  have hbne : b ≠ v := by
    intro h; rw [h, dist_self] at hbd; linarith
  have hbS : b ∉ S :=
    hεS b (by rw [mem_ball, hbd]; exact lt_of_lt_of_le hηlt (min_le_left _ _)) hbne
  obtain ⟨ε₁, hε₁, -, hJ⟩ := hUA (hVU hbV)
  have hab : JoinedIn (U \ S) a b := hJ b (mem_ball_self hε₁) hbS
  refine ⟨b, hbV, hbS, hab.somePath.toContinuousMap, hab.somePath.source, hab.somePath.target,
    fun t => hab.somePath_mem t⟩

end GoldbachBoundaries.ThmA
