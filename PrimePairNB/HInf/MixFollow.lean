import PrimePairNB.HInf.MixBoundary
import PrimePairNB.HInf.MixFollowCommon

/-! Continuation and near-line non-vacuity for the mixed prime series. -/
noncomputable section
open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf

/-- The uniform mixed sheet family continues the series throughout its domain. -/
theorem continuesAlong_mix_vinf (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (hγ : ∀ t, γ t ∈ VInf ⊤ \ Pinch)
    (h0 : 2 < (γ 0).re) : ContinuesAlong MixSer γ := by
  have hstart : GermFamMix 0 (γ 0) MixSer := by
    refine ⟨0, mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ h0,
      0, zero_mem _, ?_⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0] with v hv
    simp [MixProof.Dth_eq hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0 hv]
  obtain ⟨f, hf, hf0, -⟩ := ThmA.exists_continuationAlong_of_uniform
    (MixProof.uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0) hγ hstart
  exact ⟨f, hf, hf0⟩

/-- Every path in the admissible region from the convergence half-plane admits continuation. -/
theorem continuesAlong_mix (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)}
    (hγ : ∀ t, γ t ∈ Aff.idL.HL \ catalogueL Aff.idL)
    (h0 : 2 < (γ 0).re) : ContinuesAlong MixSer γ := by
  apply continuesAlong_mix_vinf hZ1 hZ2 hZ3 hZ6 (h0 := h0)
  intro t
  have ht := hγ t
  rw [M4b.idL_HL_eq] at ht
  have hre : 1 < (γ t).re := ht.1
  rw [VInf_eq_of_Hinf hZ1 hH]
  exact ⟨⟨hre, EReal.coe_lt_top _⟩, fun hp => ht.2 (mem_catG_iff.mpr ⟨hre, hp⟩)⟩

/-- Any continuation from the convergence half-plane has an admissible endpoint off the catalogue. -/
theorem every_path_mix (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {γ : C(unitInterval, ℂ)}
    (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm MixSer γ g)
    (h1 : γ 1 ∉ catalogueL Aff.idL) : AdmMix g (γ 1) := by
  apply (MixProof.admMix_iff _ _).mpr
  exact Follow.every_path hH hZ1 (fun _ hs => MixSer_analyticAt hs)
    (fun g s hg => boundary_mix hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 g s
      ((MixProof.admMix_iff _ _).mpr hg)) h0 hg h1

/-- Exactly the points of the admissible region carry mixed admissible germs. -/
theorem exists_admMix_iff (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {s₁ : ℂ} : (∃ g : ℂ → ℂ, AdmMix g s₁) ↔
      s₁ ∈ Aff.idL.HL \ catalogueL Aff.idL := by
  simp only [MixProof.admMix_iff, M4b.idL_HL_eq]
  apply Follow.exists_adm_iff
  intro γ hγ h0
  exact continuesAlong_mix hH hZ1 hZ2 hZ3 hZ6
    (by simpa only [M4b.idL_HL_eq] using hγ) h0

/-- Every disc centred on `Re s = 1` contains an admissible mixed germ. -/
theorem exists_admMix_near (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∀ y : ℝ, ∀ r : ℝ, 0 < r → ∃ (s₁ : ℂ) (g : ℂ → ℂ),
      s₁ ∈ ball (1 + (y : ℂ) * I) r ∧ AdmMix g s₁ := by
  have hex : ∀ s ∈ HH \ catG, ∃ g : ℂ → ℂ, Follow.Adm MixSer g s := by
    intro s hs
    obtain ⟨g, hg⟩ := (exists_admMix_iff hH hZ1 hZ2 hZ3 hZ6).mpr
      (by simpa only [M4b.idL_HL_eq] using hs)
    exact ⟨g, (MixProof.admMix_iff _ _).mp hg⟩
  intro y r hr
  obtain ⟨s, g, hs, hg⟩ := Follow.exists_adm_near hex y r hr
  exact ⟨s, g, hs, (MixProof.admMix_iff _ _).mpr hg⟩

end GoldbachBoundaries.HInf

