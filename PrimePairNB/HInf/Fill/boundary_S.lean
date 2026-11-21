import PrimePairNB.HInf.Fill.boundary_G
import PrimePairNB.HInf.Fill.germFam_of_admissible_S
import PrimePairNB.HInf.Fill.admS_transfer
import PrimePairNB.HInf.Fill.deriv_Xc_S
import PrimePairNB.HInf.Fill.prop71_S

/-!
# `boundary_S`

The shape of `boundary_G`, with the variable change `v = 2s + 1` between the two planes. `prop71_S` gives `x` near
`1 + 2iy` with `X_x'(x) ≠ 0`. A path in the `s`-disc, off the poles of the extension and off `catS`, carries the germ to the
preimage of the slit disc at `x`. `admS_transfer` moves the germ to the variable `v`, where `germFam_of_admissible_S`
puts it in `𝔊`, and `not_analytic_of_germFam` applies.

The helpers on `AdmS` here are used by the other `S` files of this group.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma admS_congr {g g' : ℂ → ℂ} {s : ℂ} (h : AdmS g s) (hgg : g =ᶠ[𝓝 s] g') : AdmS g' s := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := h
  exact ⟨γ, hγ, h0, rfl, f, hf, hf0, hgg.symm.trans hg1⟩

lemma admS_mem {g : ℂ → ℂ} {s : ℂ} (h : AdmS g s) : s ∈ halfPlane 0 \ catS := by
  obtain ⟨γ, hγ, -, rfl, -⟩ := h
  exact hγ 1

lemma admS_analyticAt {g : ℂ → ℂ} {s : ℂ} (h : AdmS g s) : AnalyticAt ℂ g s := by
  obtain ⟨γ, -, -, rfl, f, hf, -, hg1⟩ := h
  exact (hf.analyticAt 1).congr hg1.symm

/-- Continue an admissible germ along a path off the catalogue. -/
lemma admS_trans {g g' : ℂ → ℂ} {s : ℂ} (hg : AdmS g s) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s)
    (hγ : ∀ t, γ t ∈ halfPlane 0 \ catS) (hg' : IsTerminalGerm g γ g') : AdmS g' (γ 1) := by
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := ThmA.isTerminalGerm_trans_proof hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

/-- `S` is admissible at each point of `σ > 1`, along the constant path. -/
lemma admS_of_one_lt {w : ℂ} (hw : 1 < w.re) : AdmS Sser w := by
  have hH : w ∈ halfPlane 0 \ catS :=
    ⟨show (0 : ℝ) < w.re by linarith, fun hc => by linarith [re_le_half_of_mem_catS hc]⟩
  have hw2 : 1 / 2 < w.re := by linarith
  exact ⟨ContinuousMap.const _ w, fun _ => hH, hw, rfl,
    ThmA.isTerminalGerm_of_analyticAt (fun _ => Sser_analyticAt hw2) EventuallyEq.rfl⟩

/-- Under `(H_∞)`, near a point of `σ > 0` no other point has `2s + 1 ∈ Σ + Σ`. -/
lemma eventually_not_pinch_S (hZ1 : Z1) (hH : Hinf) {z : ℂ} (hz : 0 < z.re) :
    ∀ᶠ w in 𝓝[≠] z, 2 * w + 1 ∉ Pinch := by
  have hre : 1 < (2 * z + 1).re := by
    simp only [add_re, one_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have ht : Tendsto (fun w : ℂ => 2 * w + 1) (𝓝[≠] z) (𝓝[≠] (2 * z + 1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : ContinuousAt (fun w : ℂ => 2 * w + 1) z := by fun_prop
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw h
      apply hw
      have h' : 2 * w + 1 = 2 * z + 1 := h
      have h2 : (2 : ℂ) * w = 2 * z := add_right_cancel h'
      exact mul_left_cancel₀ two_ne_zero h2
  exact ht.eventually (eventually_not_pinch hZ1 hH hre)

lemma eventually_not_catS (hZ1 : Z1) (hH : Hinf) {z : ℂ} (hz : 0 < z.re) : ∀ᶠ w in 𝓝[≠] z, w ∉ catS := by
  filter_upwards [eventually_not_pinch_S hZ1 hH hz] with w hw hc
  exact hw (mem_catS_iff.mp hc).2

lemma codiscrete_not_catS (hZ1 : Z1) (hH : Hinf) : ∀ᶠ z in codiscreteWithin (halfPlane 0), z ∉ catS := by
  rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  filter_upwards [eventually_not_catS hZ1 hH hz] with w hw
  exact Or.inl hw

/-- `‖(v - 1)/2 - (x - 1)/2‖ = ‖v - x‖ / 2`. -/
lemma dist_half_sub_one (v x : ℂ) : dist ((v - 1) / 2) ((x - 1) / 2) = dist v x / 2 := by
  rw [dist_eq_norm, dist_eq_norm, show (v - 1) / 2 - (x - 1) / 2 = (v - x) / 2 by ring, norm_div]
  norm_num

/-- `‖(2s + 1) - x‖ = 2 ‖s - (x - 1)/2‖`. -/
lemma dist_two_mul_add_one (s x : ℂ) : dist (2 * s + 1) x = 2 * dist s ((x - 1) / 2) := by
  rw [dist_eq_norm, dist_eq_norm, show 2 * s + 1 - x = 2 * (s - (x - 1) / 2) by ring, norm_mul]
  norm_num

/-- The point of `prop71_S` in a disc on the line `Re v = 1`: `x ∈ X`, `x` in the disc, `X_x'(x) ≠ 0`. -/
lemma exists_good_pinch_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Xcat, x ∈ Vt 3 ∧ x ∈ ball (1 + (y : ℂ) * I) r ∧ deriv (Xc kS x) x ≠ 0 := by
  obtain ⟨x, ρ, hρ, hρre, q, hq, hx, hxD, hne⟩ :=
    (prop71_S hZ1 hZ2 hZ4 hZ5 (M1.lem_B_iii_proof hH) y (min r 1) (lt_min hr one_pos)).nonempty
  have hρq : ρ / (q : ℂ) ∈ PoleSetQ := Or.inr ⟨q, hq.one_lt.le, hq.squarefree, ρ, hρ, rfl⟩
  have hPin : x ∈ Pinch := ⟨1, Or.inl (Or.inl rfl), ρ / (q : ℂ), hρq, hx⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hre : 1 < x.re := by
    have h1 : (ρ / (q : ℂ)).re = ρ.re / q := Complex.div_natCast_re ρ q
    rw [hx, add_re, one_re, h1, hρre]
    have : 0 < (1 / 2 : ℝ) / q := by positivity
    linarith
  have hxcat : x ∈ Xcat := ⟨hPin, by rw [M2.Binf_eq_half_of_Hinf hZ1 hH]; linarith⟩
  have hlt : x.re < 3 := by
    have h1 : |(x - (1 + (y : ℂ) * I)).re| ≤ ‖x - (1 + (y : ℂ) * I)‖ := Complex.abs_re_le_norm _
    have h2 : ‖x - (1 + (y : ℂ) * I)‖ < min r 1 := by rw [← dist_eq_norm]; exact hxD
    have h3 : ‖x - (1 + (y : ℂ) * I)‖ < 1 := lt_of_lt_of_le h2 (min_le_right _ _)
    have h4 : (x - (1 + (y : ℂ) * I)).re = x.re - 1 := by simp
    rw [h4] at h1
    linarith [(abs_le.mp h1).2]
  have hxV : x ∈ Vt 3 := ⟨hre, (EReal.coe_lt_coe_iff.mpr hlt).trans_eq (by norm_cast)⟩
  refine ⟨x, hxcat, hxV, ball_subset_ball (min_le_left _ _) hxD, ?_⟩
  rw [deriv_Xc_S hZ1 hxcat hxV]
  exact mul_ne_zero (by norm_num) hne

/-- No (Z6). -/
theorem boundary_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmS g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball ((y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball ((y : ℂ) * I) r) := by
  rintro ⟨-, f, hfm, hfg⟩
  have hs₁m := admS_mem hg
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := ThmA.exists_meromorphic_update hfm hfg
  -- step 1: the point `x`, in `v`, a generic slope, the local statement at `x`
  obtain ⟨x, hxcat, hxV, hxD, hX⟩ :=
    exists_good_pinch_S hH hZ1 hZ2 hZ4 hZ5 (2 * y) (r := 2 * r) (by linarith)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, IsGenericSlope κ := by
    obtain ⟨κ, hκ⟩ := (generic_cocountable.dense_compl ℝ).nonempty
    exact ⟨κ, by simpa using hκ⟩
  obtain ⟨rx, hrx, -, hna⟩ :=
    not_analytic_of_germFam hZ1 hZ2 hZ3 isPinchKernel_S hκ hxcat hxV hX
  -- the point of the disc in `s` over `x`
  set c : ℂ := (x - 1) / 2 with hc
  set D := ball ((y : ℂ) * I) r with hD
  have hcD : c ∈ D := by
    have h1 : dist c ((1 + ((2 * y : ℝ) : ℂ) * I - 1) / 2) = dist x (1 + ((2 * y : ℝ) : ℂ) * I) / 2 :=
      dist_half_sub_one _ _
    have h2 : (1 + ((2 * y : ℝ) : ℂ) * I - 1) / 2 = (y : ℂ) * I := by
      push_cast
      ring
    rw [h2] at h1
    have h3 : dist x (1 + ((2 * y : ℝ) : ℂ) * I) < 2 * r := hxD
    rw [hD, mem_ball, h1]
    linarith
  obtain ⟨ε₁, hε₁, hε₁an⟩ : ∃ ε₁ > 0, ∀ z ∈ ball c ε₁, z ≠ c → AnalyticAt ℂ f' z := by
    have h := (hf'm c hcD).eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
    exact ⟨ε, hε, fun z hz hne => hball z hz hne⟩
  obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.mp isOpen_ball c hcD
  have hx1 : 0 < x.re - 1 := sub_pos.mpr hxV.1
  have hx3 : x.re < 3 := re_lt_three_of_mem hxV
  set ε₀ := min rx (min (2 * ε₁) (min (2 * ε₂) (min (x.re - 1) (3 - x.re)))) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hrx (lt_min (by linarith) (lt_min (by linarith) (lt_min hx1 (by linarith))))
  have hε₀r : ε₀ ≤ rx := min_le_left _ _
  have hε₀1 : ε₀ ≤ 2 * ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ 2 * ε₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀α : ε₀ ≤ x.re - 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₀3 : ε₀ ≤ 3 - x.re :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- step 2: a path from `s₁` to the preimage of the slit disc, off the poles of `f'` and off `catS`
  set S : Set ℂ := {z | ¬ AnalyticAt ℂ f' z} ∪ catS with hS
  have hUo : IsOpen (D ∩ halfPlane 0) := isOpen_ball.inter (isOpen_halfPlane 0)
  have hUc : IsConnected (D ∩ halfPlane 0) :=
    ⟨⟨s₁, hs₁, hs₁m.1⟩, ((convex_ball _ _).inter (convex_halfSpace_re_gt (0 : ℝ))).isPreconnected⟩
  have hSc : ∀ᶠ z in codiscreteWithin (D ∩ halfPlane 0), z ∉ S := by
    have h1 : ∀ᶠ z in codiscreteWithin (D ∩ halfPlane 0), AnalyticAt ℂ f' z :=
      codiscreteWithin_mono inter_subset_left hf'an
    have h2 : ∀ᶠ z in codiscreteWithin (D ∩ halfPlane 0), z ∉ catS :=
      codiscreteWithin_mono inter_subset_right (codiscrete_not_catS hZ1 hH)
    filter_upwards [h1, h2] with z hz1 hz2
    rintro (h | h)
    · exact h hz1
    · exact hz2 h
  have hs₁S : s₁ ∉ S := by
    rintro (h | h)
    · exact h ((admS_analyticAt hg).congr hf'g.symm)
    · exact hs₁m.2 h
  set V := ball x ε₀ \ rayW κ x with hV
  have hVeq : V = slitDisc (slantDir κ) x ε₀ := (slitDisc_eq hε₀α).symm
  have hVo : IsOpen V := by rw [hVeq]; exact (ThmA.slitDisc_facts κ hε₀pos hε₀α).1
  have hVne : V.Nonempty := by
    obtain ⟨s, hs, -⟩ := ThmA.exists_mem_slitDisc κ (α := x) hε₀pos
    exact ⟨s, hVeq ▸ hs⟩
  set V' : Set ℂ := (fun s : ℂ => 2 * s + 1) ⁻¹' V with hV'
  have hV'o : IsOpen V' := hVo.preimage (by fun_prop)
  have hV'ne : V'.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨(v - 1) / 2, ?_⟩
    show 2 * ((v - 1) / 2) + 1 ∈ V
    rwa [show 2 * ((v - 1) / 2) + 1 = v by ring]
  have hV'U : V' ⊆ D ∩ halfPlane 0 := by
    intro s hs
    have hsb : dist (2 * s + 1) x < ε₀ := hs.1
    have hdist := dist_two_mul_add_one s x
    refine ⟨hε₂D ?_, ?_⟩
    · rw [mem_ball]
      linarith
    · have h1 : |(2 * s + 1 - x).re| ≤ ‖2 * s + 1 - x‖ := Complex.abs_re_le_norm _
      have h2 : ‖2 * s + 1 - x‖ < ε₀ := by rw [← dist_eq_norm]; exact hsb
      have h3 : (2 * s + 1 - x).re = 2 * s.re + 1 - x.re := by simp
      rw [h3] at h1
      have h4 := (abs_le.mp h1).1
      show (0 : ℝ) < s.re
      linarith
  obtain ⟨s₂, hs₂V, -, γ, hγ0, hγ1, hγ⟩ :=
    ThmA.exists_path_into hUo hUc hSc ⟨hs₁, hs₁m.1⟩ hs₁S hV'o hV'ne hV'U
  have hterm : IsTerminalGerm g γ f' := ThmA.isTerminalGerm_of_analyticAt
    (fun t => by by_contra h; exact (hγ t).2 (Or.inl h)) (by rw [hγ0]; exact hf'g)
  have hadm : AdmS f' (γ 1) := admS_trans hg γ hγ0
    (fun t => ⟨(hγ t).1.2, fun h => (hγ t).2 (Or.inr h)⟩) hterm
  rw [hγ1] at hadm
  -- step 3: in `v`, the germ at `2 s₂ + 1` is in `𝔊`, and it is analytic across the cut
  have hqV : 2 * s₂ + 1 ∈ V := hs₂V
  have hq3 : (2 * s₂ + 1).re < 3 := by
    have h1 : |(2 * s₂ + 1 - x).re| ≤ ‖2 * s₂ + 1 - x‖ := Complex.abs_re_le_norm _
    have h2 : ‖2 * s₂ + 1 - x‖ < ε₀ := by rw [← dist_eq_norm]; exact hqV.1
    have h3 := (abs_le.mp h1).2
    have h4 : (2 * s₂ + 1 - x).re = (2 * s₂ + 1).re - x.re := Complex.sub_re _ _
    rw [h4] at h3
    linarith
  obtain ⟨C, hC⟩ := germFam_of_admissible_S hZ1 hZ2 hZ3 (admS_transfer hZ1 hH hadm) hq3
  refine hna ε₀ hε₀pos hε₀r (fun v => f' ((v - 1) / 2)) (fun v hv hne => ?_) _ hqV C hC
  have hv1 : dist ((v - 1) / 2) c = dist v x / 2 := dist_half_sub_one v x
  have hv2 : dist v x < ε₀ := hv
  have hvb : (v - 1) / 2 ∈ ball c ε₁ := by
    rw [mem_ball, hv1]
    linarith
  have hvne : (v - 1) / 2 ≠ c := by
    intro h
    apply hne
    have h' : (v - 1) / 2 * 2 = (x - 1) / 2 * 2 := by rw [h]
    have h'' : v - 1 = x - 1 := by
      have e1 : (v - 1) / 2 * 2 = v - 1 := by ring
      have e2 : (x - 1) / 2 * 2 = x - 1 := by ring
      rwa [e1, e2] at h'
    exact sub_left_inj.mp h''
  have han := analyticAt_comp_half (hε₁an _ hvb hvne)
  rwa [show 2 * ((v - 1) / 2) + 1 = v by ring] at han

end GoldbachBoundaries.HInf.Fill

