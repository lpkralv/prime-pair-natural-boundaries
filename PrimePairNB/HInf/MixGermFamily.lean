import PrimePairNB.HInf.MixRotation
import PrimePairNB.HInf.Fill.uniformFamily_germFam
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- **One slope suffices.** For any `κ'` with `q ∈ Ω_κ'`, a member of `𝔊(q)` has the form
`D^{κ'} + m + C` with that `κ'`. -/
theorem germFam_slope (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) {C q : ℂ} {f : ℂ → ℂ} (h : GermFamMix C q f) {κ' : ℝ} (hκ' : q ∈ Om κ' ⊤) :
    ∃ m ∈ MSpanMix, f =ᶠ[𝓝 q] fun v => DthMix κ' v + m v + C := by
  obtain ⟨κ, hκ, m, hm, hf⟩ := h
  rcases lt_trichotomy κ κ' with hlt | rfl | hlt
  · obtain ⟨hfin, hrot⟩ := rotation hZ1 hZ2 hZ3 hK hlt hκ hκ'
    refine ⟨m - sumMcMix (sector q κ κ'), sub_mem hm (sumMc_mem hfin), ?_⟩
    filter_upwards [hf, hrot] with v hv hr
    rw [hv, hr, Pi.sub_apply]
    ring
  · exact ⟨m, hm, hf⟩
  · obtain ⟨hfin, hrot⟩ := rotation hZ1 hZ2 hZ3 hK hlt hκ' hκ
    refine ⟨m + sumMcMix (sector q κ' κ), add_mem hm (sumMc_mem hfin), ?_⟩
    filter_upwards [hf, hrot] with v hv hr
    rw [hv, hr, Pi.add_apply]
    ring

/-- **The step.** `𝔊` is a uniform germ family on `𝒱_∞ ∖ X`, in the sense of `ThmA.UniformFamily`. -/
theorem uniformFamily_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) (C : ℂ) : ThmA.UniformFamily (GermFamMix C) (VInf ⊤ \ Pinch) := by
  intro p hp
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ, p ∈ Om κ₀ ⊤ := by
    obtain ⟨κ₀, hκ₀⟩ := ((countable_not_mem_Om hp.1 hp.2).dense_compl ℝ).nonempty
    exact ⟨κ₀, by simpa using hκ₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_Om hZ1 κ₀ ⊤) p hκ₀
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  obtain ⟨m, hm, hfm⟩ := germFam_slope hZ1 hZ2 hZ3 hK hf (hball hq)
  have hA : AnalyticOnNhd ℂ (fun v => DthMix κ₀ v + m v + C) (ball p r) := fun z hz =>
    ((Dth_analyticOn hZ1 hZ2 hZ3 hK κ₀ z (hball hz)).add
      (MSpanK_analyticOn hZ1 hK hm z (hball hz).1.1)).add analyticAt_const
  exact ⟨_, hA, hfm.symm, fun q' hq' => ⟨κ₀, hball hq', m, hm, EventuallyEq.rfl⟩⟩

/-- **Local form.** Near `x ∈ X`, every member of `𝔊` is `Log_θ(v - x) X_x + holomorphic`, with the same
`X_x` on every branch. `r` depends on `κ` and `x`, not on the germ. -/
theorem local_form_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt ⊤) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf ⊤ ∧ ball x r \ rayW κ x ⊆ Om κ ⊤ ∧
      ∀ q ∈ ball x r \ rayW κ x, ∀ (C : ℂ) (f : ℂ → ℂ), GermFamMix C q f →
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball x r) ∧
          f =ᶠ[𝓝 q] fun v => logK κ (v - x) * XcMix x v + h v := by
  obtain ⟨r, hr, hsub, hslit, H, hH, hform⟩ := local_model hZ1 hZ2 hZ3 hK hκ hx hxV
  refine ⟨r, hr, hsub, hslit, fun q hq C f hf => ?_⟩
  obtain ⟨m, hm, hfm⟩ := germFam_slope hZ1 hZ2 hZ3 hK hf (hslit hq)
  refine ⟨fun v => H v + m v + C, fun z hz =>
    ((hH z hz).add (MSpanK_analyticOn hZ1 hK hm z (hsub hz).1)).add analyticAt_const, ?_⟩
  have hnear : ∀ᶠ v in 𝓝 q, v ∈ ball x r \ rayW κ x := by
    filter_upwards [isOpen_ball.mem_nhds hq.1, (isOpen_Om hZ1 κ ⊤).mem_nhds (hslit hq)] with v hv hOm
    exact ⟨hv, fun hray => hOm.2 (mem_iUnion₂.mpr ⟨x, hx.1, hray⟩)⟩
  filter_upwards [hfm, hnear] with v h1 h2
  rw [h1, hform v h2]
  ring

end GoldbachBoundaries.HInf.MixProof
