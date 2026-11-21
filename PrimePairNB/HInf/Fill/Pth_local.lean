import PrimePairNB.HInf.Fill.hasDerivAt_Pth

/-! Proof of `Pth_local`.

`Q = R_a/(z-a) + g` near `a` with `g` analytic (`M1.hasResidue_Qcont_Rcoef`, order `≥ 0` of the difference). With `Φ` a
primitive of `g` on a small ball, `P^θ` and `c(a) Log_θ(z-a) - Φ` have the same derivative on the slit disc, which is
open and connected, so they differ by a constant. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

private lemma slantDir_ne_zero' (κ : ℝ) : slantDir κ ≠ 0 := ThmA.slantDir_ne_zero κ

/-- Off the ray means `(z - a)/w` is in the slit plane. -/
lemma not_mem_rayW_iff (κ : ℝ) (a z : ℂ) :
    z ∉ rayW κ a ↔ (z - a) / slantDir κ ∈ slitPlane := by
  have hv := slantDir_ne_zero' κ
  constructor
  · intro hcut
    by_contra hslit
    have hnot : ¬ (0 < ((z - a) / slantDir κ).re ∨ ((z - a) / slantDir κ).im ≠ 0) := by
      simpa only [Complex.mem_slitPlane_iff] using hslit
    have hre : ((z - a) / slantDir κ).re ≤ 0 := le_of_not_gt (fun h => hnot (Or.inl h))
    have him : ((z - a) / slantDir κ).im = 0 := not_not.mp (fun h => hnot (Or.inr h))
    have hreal : (z - a) / slantDir κ = ((((z - a) / slantDir κ).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have hid : (z - a) / slantDir κ * slantDir κ = z - a := div_mul_cancel₀ _ hv
    rw [hreal] at hid
    refine hcut ⟨-((z - a) / slantDir κ).re, neg_nonneg.mpr hre, ?_⟩
    push_cast
    linear_combination -hid
  · rintro hslit ⟨t, ht, he⟩
    have heq : (z - a) / slantDir κ = -(t : ℂ) := by
      rw [he]
      field_simp
      ring
    rw [heq, Complex.mem_slitPlane_iff] at hslit
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
      ne_self_iff_false, or_false, neg_pos] at hslit
    exact not_lt_of_ge ht hslit

/-- The slit disc is open and connected (star-shaped about a point on the opposite radius). -/
lemma slit_facts (κ : ℝ) (a : ℂ) {R : ℝ} (hR : 0 < R) :
    IsOpen (ball a R \ rayW κ a) ∧ IsPreconnected (ball a R \ rayW κ a) := by
  have hv := slantDir_ne_zero' κ
  let q : ℂ → ℂ := fun s => (s - a) / slantDir κ
  have hq : Continuous q := by fun_prop
  have hset : ball a R \ rayW κ a = ball a R ∩ q ⁻¹' slitPlane := by
    ext s
    exact and_congr_right fun _ => not_mem_rayW_iff κ a s
  rw [hset]
  refine ⟨isOpen_ball.inter (isOpen_slitPlane.preimage hq), ?_⟩
  have hnv : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hv
  let c : ℝ := R / (2 * ‖slantDir κ‖)
  have hc : 0 < c := by dsimp [c]; positivity
  let p : ℂ := a + (c : ℂ) * slantDir κ
  have hqp : q p = (c : ℂ) := by simp [q, p, hv]
  have hp : p ∈ ball a R := by
    rw [mem_ball, dist_eq_norm]
    simp only [p, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    field_simp
    linarith
  have hstar : StarConvex ℝ p (q ⁻¹' slitPlane) := by
    intro y hy s t hs ht hst
    have h := (Complex.starConvex_ofReal_slitPlane hc) hy hs ht hst
    change q (s • p + t • y) ∈ slitPlane
    convert h using 1
    have hstC : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    simp only [Complex.real_smul]
    rw [← hqp]
    dsimp [q]
    field_simp
    linear_combination a * hstC
  exact ((convex_ball a R).starConvex hp).inter hstar
    |>.isPathConnected ⟨hp, by change q p ∈ slitPlane; rw [hqp]; exact ofReal_mem_slitPlane.mpr hc⟩
    |>.isConnected.isPreconnected

/-- `Q - R_a/(z-a)` extends analytically across `a`. -/
lemma exists_regular_part {a : ℂ} (ha : a ∈ PoleSetQ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, g z = Qcont z - Rcoef a / (z - a) := by
  have ha0 : 0 < a.re := (M1.poleSetQ_re_bounds ha).1
  set f : ℂ → ℂ := fun z => Qcont z - Rcoef a / (z - a) with hf
  have hsub : MeromorphicAt (fun s : ℂ => s - a) a :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hm : MeromorphicAt f a :=
    (meromorphicAt_Qcont ha0).sub (MeromorphicAt.const _ a |>.div hsub)
  have hres : HasResidue f a 0 := by
    have := (M1.hasResidue_Qcont_Rcoef ha).sub (hasResidue_div_sub a (Rcoef a))
    simpa using this
  have hprod : MeromorphicAt ((fun s : ℂ => s - a) * f) a := hsub.mul hm
  have h0 : 0 < meromorphicOrderAt ((fun s : ℂ => s - a) * f) a :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hprod).1 hres
  rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const] at h0
  have hord : 0 ≤ meromorphicOrderAt f a := by
    cases ho : meromorphicOrderAt f a with
    | top => exact le_top
    | coe n =>
      rw [ho] at h0
      have h1 : (0 : ℤ) < 1 + n := by exact_mod_cast h0
      exact_mod_cast (by omega : (0 : ℤ) ≤ n)
  refine ⟨toMeromorphicNFAt f a, (hm.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).1 hord, ?_⟩
  filter_upwards [hm.eq_nhdsNE_toMeromorphicNFAt] with z hz
  exact hz.symm

lemma hasDerivAt_logK {κ : ℝ} {a z : ℂ} (hz : z ∉ rayW κ a) :
    HasDerivAt (fun u => logK κ (u - a)) (1 / (z - a)) z := by
  have hv := slantDir_ne_zero' κ
  have hs : (z - a) / slantDir κ ∈ slitPlane := (not_mem_rayW_iff κ a z).1 hz
  have hza : z - a ≠ 0 := by
    intro h
    rw [h, zero_div] at hs
    exact Complex.zero_notMem_slitPlane hs
  have h0 : HasDerivAt (fun u : ℂ => (u - a) / slantDir κ) (1 / slantDir κ) z :=
    ((hasDerivAt_id z).sub_const a).div_const _
  have h1 := (h0.clog hs).add_const (Complex.log (slantDir κ))
  have e : 1 / slantDir κ / ((z - a) / slantDir κ) = 1 / (z - a) := by
    field_simp
  rw [e] at h1
  exact h1

/-- If `a` is the only point of `Σ` on its `κ`-line, then for small `R`, off the cut,
`P^θ(z) = c(a) Log_θ(z - a) + E_a(z)` with `E_a` holomorphic on the disc, and the slit disc lies in `U_θ`. -/
theorem Pth_local {κ : ℝ} {a : ℂ} (ha : a ∈ PoleSetQ)
    (hsole : ∀ a' ∈ PoleSetQ, a' ≠ a → ∀ t : ℝ, a' - a ≠ (t : ℂ) * slantDir κ) :
    ∃ R : ℝ, 0 < R ∧ ball a R ⊆ halfPlane 0 ∧ ball a R \ rayW κ a ⊆ Uth κ ∧
      ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball a R) ∧
        ∀ z ∈ ball a R \ rayW κ a, Pth κ z = cP a * logK κ (z - a) + E z := by
  have ha0 : 0 < a.re := (M1.poleSetQ_re_bounds ha).1
  obtain ⟨S, hSf, hSP, key⟩ := exists_finite_cuts κ ha0
  set C : Set ℂ := ⋃ a' ∈ S \ {a}, rayW κ a' with hC
  have hCc : IsClosed C := (hSf.subset sdiff_subset).isClosed_biUnion fun a' _ => isClosed_rayW_Uth κ a'
  have haC : a ∉ C := by
    intro h
    obtain ⟨a', ⟨haS, hne⟩, t, ht, he⟩ := mem_iUnion₂.mp h
    exact hsole a' (hSP haS) hne t (by linear_combination -he)
  obtain ⟨r₁, hr₁, hr₁C⟩ := Metric.isOpen_iff.mp hCc.isOpen_compl a haC
  obtain ⟨g, hg, hgeq⟩ := exists_regular_part ha
  obtain ⟨r₂, hr₂, hg2⟩ := hg.exists_ball_analyticOnNhd
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hgeq
  obtain ⟨r₃, hr₃, hg3⟩ := hgeq
  set R : ℝ := min (a.re / 2) (min r₁ (min r₂ r₃)) with hRdef
  have hR : 0 < R := by
    simp only [hRdef, lt_min_iff]
    exact ⟨by positivity, hr₁, hr₂, hr₃⟩
  have hR0 : R ≤ a.re / 2 := min_le_left _ _
  have hR1 : R ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hR2 : R ≤ r₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR3 : R ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hball0 : ball a R ⊆ halfPlane 0 := by
    intro z hz
    have hzz : ‖z - a‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - a).re| ≤ ‖z - a‖ := Complex.abs_re_le_norm _
    have h2 := (abs_le.mp h1).1
    show 0 < z.re
    simp only [sub_re] at h2
    linarith
  have hUsub : ball a R \ rayW κ a ⊆ Uth κ := by
    rintro z ⟨hzb, hzr⟩
    refine ⟨hball0 hzb, fun h => ?_⟩
    obtain ⟨a', ha', hza'⟩ := mem_iUnion₂.mp h
    by_cases hne : a' = a
    · exact hzr (hne ▸ hza')
    · have hzC : z ∈ Cᶜ := hr₁C (ball_subset_ball hR1 hzb)
      exact hzC (mem_iUnion₂.mpr
        ⟨a', ⟨key z (ball_subset_ball hR0 hzb) a' ha' hza', hne⟩, hza'⟩)
  have hgd : DifferentiableOn ℂ g (ball a R) := fun z hz =>
    (hg2 z (ball_subset_ball hR2 hz)).differentiableAt.differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := M6.B_exists_primitive_ball hgd
  obtain ⟨hUo, hUc⟩ := slit_facts κ a hR
  set f₂ : ℂ → ℂ := fun z => cP a * logK κ (z - a) - Φ z with hf₂
  have hd2 : ∀ z ∈ ball a R \ rayW κ a, HasDerivAt f₂ (-Qcont z) z := by
    rintro z ⟨hzb, hzr⟩
    have hzne : z ≠ a := by
      rintro rfl
      exact hzr ⟨0, le_rfl, by simp⟩
    have h1 := ((hasDerivAt_logK hzr).const_mul (cP a)).sub (hΦ z hzb)
    have hge : g z = Qcont z - Rcoef a / (z - a) := hg3 z (ball_subset_ball hR3 hzb) hzne
    have e : cP a * (1 / (z - a)) - g z = -Qcont z := by
      rw [hge, cP]
      ring
    rw [e] at h1
    exact h1
  have hd1 : ∀ z ∈ ball a R \ rayW κ a, HasDerivAt (Pth κ) (-Qcont z) z := fun z hz =>
    hasDerivAt_Pth (hUsub hz)
  obtain ⟨c, hc⟩ := hUo.exists_eq_add_of_deriv_eq hUc
    (fun z hz => (hd1 z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd2 z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hd1 z hz).deriv, (hd2 z hz).deriv])
  refine ⟨R, hR, hball0, hUsub, fun z => -Φ z + c, ?_, fun z hz => ?_⟩
  · have hE : DifferentiableOn ℂ (fun z => -Φ z + c) (ball a R) := fun z hz =>
      ((hΦ z hz).differentiableAt.neg.add_const c).differentiableWithinAt
    exact hE.analyticOnNhd isOpen_ball
  · have := hc hz
    simp only [hf₂] at this
    rw [this]
    ring

end GoldbachBoundaries.HInf.Fill
