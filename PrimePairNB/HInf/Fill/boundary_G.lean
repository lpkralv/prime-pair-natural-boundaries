import PrimePairNB.HInf.Fill.not_analytic_of_germFam
import PrimePairNB.HInf.Fill.germFam_of_admissible_G
import PrimePairNB.HInf.Fill.deriv_Xc_G
import PrimePairNB.HInf.Fill.prop71_G
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-!
# `boundary_G`

The shape of `ThmA.thm_G_boundary_proof`. `prop71_G` gives `x` in the disc with `X_x'(x) = pairSum x ≠ 0`. A path in the disc,
off the poles of the extension and off `catG`, carries the germ to the slit disc at `x`; there the germ is in `𝔊`
(`germFam_of_admissible_G`), and `not_analytic_of_germFam` applies.

The helpers on `AdmG` here are used by the other `G` files of this group.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma mem_catG_iff {s : ℂ} : s ∈ catG ↔ 1 < s.re ∧ s ∈ Pinch := by
  have happ : Aff.idL.app s = s := by simp [Aff.app, Aff.idL]
  simp [catG, catalogueL, Aff.HL, happ]

lemma admG_congr {g g' : ℂ → ℂ} {s : ℂ} (h : AdmG g s) (hgg : g =ᶠ[𝓝 s] g') : AdmG g' s := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := h
  exact ⟨γ, hγ, h0, rfl, f, hf, hf0, hgg.symm.trans hg1⟩

lemma admG_mem {g : ℂ → ℂ} {s : ℂ} (h : AdmG g s) : s ∈ HH \ catG := by
  obtain ⟨γ, hγ, -, rfl, -⟩ := h
  exact hγ 1

lemma admG_analyticAt {g : ℂ → ℂ} {s : ℂ} (h : AdmG g s) : AnalyticAt ℂ g s := by
  obtain ⟨γ, -, -, rfl, f, hf, -, hg1⟩ := h
  exact (hf.analyticAt 1).congr hg1.symm

/-- Continue an admissible germ along a path off the catalogue. -/
lemma admG_trans {g g' : ℂ → ℂ} {s : ℂ} (hg : AdmG g s) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s)
    (hγ : ∀ t, γ t ∈ HH \ catG) (hg' : IsTerminalGerm g γ g') : AdmG g' (γ 1) := by
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := ThmA.isTerminalGerm_trans_proof hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

/-- `G` is admissible at each point of `σ > 2`, along the constant path. -/
lemma admG_of_two_lt {w : ℂ} (hw : 2 < w.re) : AdmG G w := by
  have hH : w ∈ HH \ catG :=
    ⟨show (1 : ℝ) < w.re by linarith, fun hc => by linarith [re_le_two_of_mem_pinch (mem_catG_iff.mp hc).2]⟩
  exact ⟨ContinuousMap.const _ w, fun _ => hH, hw, rfl,
    ThmA.isTerminalGerm_of_analyticAt (fun _ => ThmA.G_analyticAt hw) EventuallyEq.rfl⟩

/-- Under `(H_∞)`, `AdmG` is the hypothesis of `germFam_of_admissible_G`. -/
lemma admG_to_VInf (hZ1 : Z1) (hH : Hinf) {g : ℂ → ℂ} {s : ℂ} (hg : AdmG g s) :
    IsAdmissibleGermOn G (VInf ⊤ \ Pinch) (halfPlane 2) g s := by
  obtain ⟨γ, hγ, h0, h1, hterm⟩ := hg
  refine ⟨γ, fun t => ?_, h0, h1, hterm⟩
  have h := hγ t
  have h' : 1 < (γ t).re := h.1
  rw [VInf_eq_of_Hinf hZ1 hH]
  exact ⟨⟨h', EReal.coe_lt_top _⟩, fun hp => h.2 (mem_catG_iff.mpr ⟨h', hp⟩)⟩

/-- Under `(H_∞)`, `Σ + Σ` has no accumulation point in `σ > 1`. -/
lemma eventually_not_pinch (hZ1 : Z1) (hH : Hinf) {z : ℂ} (hz : 1 < z.re) : ∀ᶠ w in 𝓝[≠] z, w ∉ Pinch := by
  have hsub : closedBall z ((z.re - 1) / 2) ⊆ halfPlane (2 * Binf) := by
    intro s hs
    have h1 : |s.re - z.re| ≤ ‖s - z‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖s - z‖ ≤ (z.re - 1) / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hs
    have h3 := (abs_le.mp (h1.trans h2)).1
    show 2 * Binf < s.re
    rw [M2.Binf_eq_half_of_Hinf hZ1 hH]
    linarith
  have hfin := finite_inter_pinch hZ1 (isCompact_closedBall z _) hsub
  have hne : ((closedBall z ((z.re - 1) / 2) ∩ Pinch) \ {z}).Finite := hfin.subset sdiff_subset
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ (closedBall z ((z.re - 1) / 2) ∩ Pinch) \ {z} :=
    hne.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  have hball : ∀ᶠ w in 𝓝 z, w ∈ closedBall z ((z.re - 1) / 2) :=
    closedBall_mem_nhds z (by linarith)
  filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w h1 h2 h3 hp
  exact h1 ⟨⟨h2, hp⟩, h3⟩

lemma codiscrete_not_catG (hZ1 : Z1) (hH : Hinf) : ∀ᶠ z in codiscreteWithin HH, z ∉ catG := by
  rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  filter_upwards [eventually_not_pinch hZ1 hH hz] with w hw
  exact Or.inl fun hc => hw (mem_catG_iff.mp hc).2

/-- The point of `prop71_G` in a disc on the line: `x ∈ X`, `x` in the disc, `X_x'(x) ≠ 0`. -/
lemma exists_good_pinch (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Xcat, x ∈ Vt ⊤ ∧ x ∈ ball (1 + (y : ℂ) * I) r ∧ deriv (Xc kerG x) x ≠ 0 := by
  obtain ⟨x, ρ, hρ, hρre, q, hq, hx, hxD, hne⟩ :=
    (prop71_G hZ1 hZ2 hZ4 hZ5 hZ6 (M1.lem_B_iii_proof hH) y r hr).nonempty
  have hρq : ρ / (q : ℂ) ∈ PoleSetQ := Or.inr ⟨q, hq.one_lt.le, hq.squarefree, ρ, hρ, rfl⟩
  have hPin : x ∈ Pinch := ⟨1, Or.inl (Or.inl rfl), ρ / (q : ℂ), hρq, hx⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hre : 1 < x.re := by
    have h1 : (ρ / (q : ℂ)).re = ρ.re / q := Complex.div_natCast_re ρ q
    rw [hx, add_re, one_re, h1, hρre]
    have : 0 < (1 / 2 : ℝ) / q := by positivity
    linarith
  have hxcat : x ∈ Xcat := ⟨hPin, by rw [M2.Binf_eq_half_of_Hinf hZ1 hH]; linarith⟩
  have hxV : x ∈ Vt ⊤ := ⟨hre, EReal.coe_lt_top _⟩
  exact ⟨x, hxcat, hxV, hxD, by rw [deriv_Xc_G hZ1 hZ6 hxcat hxV]; exact hne⟩

/-- Proof of `HInf.boundary_G` (paper, Theorem 1.2 for `G`). -/
theorem boundary_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmG g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  rintro ⟨-, f, hfm, hfg⟩
  have hs₁m := admG_mem hg
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := ThmA.exists_meromorphic_update hfm hfg
  -- step 1: the point `x`, a generic slope, the local statement at `x`
  obtain ⟨x, hxcat, hxV, hxD, hX⟩ := exists_good_pinch hH hZ1 hZ2 hZ4 hZ5 hZ6 y hr
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, IsGenericSlope κ := by
    obtain ⟨κ, hκ⟩ := (generic_cocountable.dense_compl ℝ).nonempty
    exact ⟨κ, by simpa using hκ⟩
  obtain ⟨rx, hrx, -, hna⟩ :=
    not_analytic_of_germFam hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) hκ hxcat hxV hX
  obtain ⟨ε₁, hε₁, hε₁an⟩ : ∃ ε₁ > 0, ∀ z ∈ ball x ε₁, z ≠ x → AnalyticAt ℂ f' z := by
    have h := (hf'm x hxD).eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
    exact ⟨ε, hε, fun z hz hne => hball z hz hne⟩
  obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.mp isOpen_ball x hxD
  have hx1 : 0 < x.re - 1 := sub_pos.mpr hxV.1
  set ε₀ := min rx (min ε₁ (min ε₂ (x.re - 1))) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hrx (lt_min hε₁ (lt_min hε₂ hx1))
  have hε₀r : ε₀ ≤ rx := min_le_left _ _
  have hε₀1 : ε₀ ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ ε₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₀α : ε₀ ≤ x.re - 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- step 2: a path from `s₁` to the slit disc, off the poles of `f'` and off `catG`
  set D := ball (1 + (y : ℂ) * I) r with hD
  set S : Set ℂ := {z | ¬ AnalyticAt ℂ f' z} ∪ catG with hS
  have hUo : IsOpen (D ∩ HH) := isOpen_ball.inter (isOpen_halfPlane 1)
  have hUc : IsConnected (D ∩ HH) :=
    ⟨⟨s₁, hs₁, hs₁m.1⟩, ((convex_ball _ _).inter (convex_halfSpace_re_gt (1 : ℝ))).isPreconnected⟩
  have hSc : ∀ᶠ z in codiscreteWithin (D ∩ HH), z ∉ S := by
    have h1 : ∀ᶠ z in codiscreteWithin (D ∩ HH), AnalyticAt ℂ f' z :=
      codiscreteWithin_mono inter_subset_left hf'an
    have h2 : ∀ᶠ z in codiscreteWithin (D ∩ HH), z ∉ catG :=
      codiscreteWithin_mono inter_subset_right (codiscrete_not_catG hZ1 hH)
    filter_upwards [h1, h2] with z hz1 hz2
    rintro (h | h)
    · exact h hz1
    · exact hz2 h
  have hs₁S : s₁ ∉ S := by
    rintro (h | h)
    · exact h ((admG_analyticAt hg).congr hf'g.symm)
    · exact hs₁m.2 h
  set V := ball x ε₀ \ rayW κ x with hV
  have hVeq : V = slitDisc (slantDir κ) x ε₀ := (slitDisc_eq hε₀α).symm
  have hVo : IsOpen V := by rw [hVeq]; exact (ThmA.slitDisc_facts κ hε₀pos hε₀α).1
  have hVne : V.Nonempty := by
    obtain ⟨s, hs, -⟩ := ThmA.exists_mem_slitDisc κ (α := x) hε₀pos
    exact ⟨s, hVeq ▸ hs⟩
  have hVU : V ⊆ D ∩ HH := fun s hs =>
    ⟨hε₂D (ball_subset_ball hε₀2 hs.1), ThmA.ball_subset_HH hε₀α hs.1⟩
  obtain ⟨s₂, hs₂V, -, γ, hγ0, hγ1, hγ⟩ :=
    ThmA.exists_path_into hUo hUc hSc ⟨hs₁, hs₁m.1⟩ hs₁S hVo hVne hVU
  have hterm : IsTerminalGerm g γ f' := ThmA.isTerminalGerm_of_analyticAt
    (fun t => by by_contra h; exact (hγ t).2 (Or.inl h)) (by rw [hγ0]; exact hf'g)
  have hadm : AdmG f' (γ 1) := admG_trans hg γ hγ0
    (fun t => ⟨(hγ t).1.2, fun h => (hγ t).2 (Or.inr h)⟩) hterm
  rw [hγ1] at hadm
  -- step 3: the germ at `s₂` is in `𝔊`, and it is analytic across the cut
  exact hna ε₀ hε₀pos hε₀r f' (fun z hz hne => hε₁an z (ball_subset_ball hε₀1 hz) hne) s₂ hs₂V 0
    (germFam_of_admissible_G hZ1 hZ2 hZ3 hZ6 (admG_to_VInf hZ1 hH hadm))

end GoldbachBoundaries.HInf.Fill
