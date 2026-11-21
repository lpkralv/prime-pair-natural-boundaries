import PrimePairNB.HInf.MixContinuation
import PrimePairNB.HInf.MixObstruction
import PrimePairNB.HInf.MixArithmetic

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

lemma admMix_iff (g : ℂ → ℂ) (s : ℂ) :
    AdmMix g s ↔ IsAdmissibleGermOn MixSer (HH \ catG) (halfPlane 2) g s := by
  rw [AdmMix, M4b.idL_HL_eq, M4b.idL_RL_eq]

lemma admMix_mem {g : ℂ → ℂ} {s : ℂ} (h : AdmMix g s) : s ∈ HH \ catG := by
  rw [admMix_iff] at h
  obtain ⟨γ, hγ, -, rfl, -⟩ := h
  exact hγ 1

lemma admMix_analyticAt {g : ℂ → ℂ} {s : ℂ} (h : AdmMix g s) : AnalyticAt ℂ g s := by
  obtain ⟨γ, -, -, rfl, f, hf, -, hg1⟩ := h
  exact (hf.analyticAt 1).congr hg1.symm

/-- Continue an admissible germ along a path off the catalogue. -/
lemma admMix_trans {g g' : ℂ → ℂ} {s : ℂ} (hg : AdmMix g s) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s)
    (hγ : ∀ t, γ t ∈ HH \ catG) (hg' : IsTerminalGerm g γ g') : AdmMix g' (γ 1) := by
  rw [admMix_iff] at hg ⊢
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := ThmA.isTerminalGerm_trans_proof hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

/-- Under `(H_∞)`, `AdmMix` is the hypothesis of `germFam_of_admissible_mix`. -/
lemma admMix_to_VInf (hZ1 : Z1) (hH : Hinf) {g : ℂ → ℂ} {s : ℂ} (hg : AdmMix g s) :
    IsAdmissibleGermOn MixSer (VInf ⊤ \ Pinch) (halfPlane 2) g s := by
  rw [admMix_iff] at hg
  obtain ⟨γ, hγ, h0, h1, hterm⟩ := hg
  refine ⟨γ, fun t => ?_, h0, h1, hterm⟩
  have h := hγ t
  have h' : 1 < (γ t).re := h.1
  rw [VInf_eq_of_Hinf hZ1 hH]
  exact ⟨⟨h', EReal.coe_lt_top _⟩, fun hp => h.2 (mem_catG_iff.mpr ⟨h', hp⟩)⟩

/-- The point of `prop71_mix` in a disc on the line: `x ∈ X`, `x` in the disc, `XcMix x x ≠ 0`. -/
lemma exists_good_pinch_mix (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Xcat, x ∈ Vt ⊤ ∧ x ∈ ball (1 + (y : ℂ) * I) r ∧ XcMix x x ≠ 0 := by
  obtain ⟨x, ρ, hρ, hρre, q, hq, hx, _hsingle, hxD, hne⟩ :=
    (prop71_mix hZ1 hZ2 hZ4 hZ5 hZ6 (M1.lem_B_iii_proof hH) y r hr).nonempty
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
  exact ⟨x, hxcat, hxV, hxD, hne⟩

/-- **The boundary theorem in the pinch coordinate.** -/
theorem boundary_mix_aux (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmMix g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  rintro ⟨-, f, hfm, hfg⟩
  have hs₁m := admMix_mem hg
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := ThmA.exists_meromorphic_update hfm hfg
  -- step 1: the point `x`, a generic slope, the local statement at `x`
  obtain ⟨x, hxcat, hxV, hxD, hX⟩ := exists_good_pinch_mix hH hZ1 hZ2 hZ4 hZ5 hZ6 y hr
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
    · exact h ((admMix_analyticAt hg).congr hf'g.symm)
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
  have hadm : AdmMix f' (γ 1) := admMix_trans hg γ hγ0
    (fun t => ⟨(hγ t).1.2, fun h => (hγ t).2 (Or.inr h)⟩) hterm
  rw [hγ1] at hadm
  -- step 3: the germ at `s₂` is in `𝔊`, and it is analytic across the cut
  exact hna ε₀ hε₀pos hε₀r f' (fun z hz hne => hε₁an z (ball_subset_ball hε₀1 hz) hne) s₂ hs₂V 0
    (germFam_of_admissible_mix hZ1 hZ2 hZ3 hZ6 (admMix_to_VInf hZ1 hH hadm))

end GoldbachBoundaries.HInf.MixProof
