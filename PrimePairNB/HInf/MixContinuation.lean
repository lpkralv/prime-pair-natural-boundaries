import PrimePairNB.HInf.MixGermFamily
import PrimePairNB.HInf.MixNonvacuity
import PrimePairNB.HInf.Fill.boundary_G
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

lemma germFam_congr {C q : ℂ} {f g : ℂ → ℂ} (h : GermFamMix C q f)
    (he : f =ᶠ[𝓝 q] g) : GermFamMix C q g := by
  obtain ⟨κ, hκ, m, hm, hf⟩ := h
  exact ⟨κ, hκ, m, hm, he.symm.trans hf⟩

/-- Every admissible mixed germ belongs to the mixed sheet family. -/
lemma germFam_of_admissible_mix (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn MixSer (VInf ⊤ \ Pinch) (halfPlane 2) g q) :
    GermFamMix 0 q g := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  have hstart : GermFamMix 0 (γ 0) MixSer := by
    have h2 : 2 < (γ 0).re := h0
    refine ⟨0, mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ h2, 0, zero_mem _, ?_⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with v hv
    simp [Dth_eq hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0 hv]
  exact germFam_congr (ThmA.continuationAlong_preserve
    (uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0)
    (fun _ _ _ h hfg => germFam_congr h hfg) hγ hf
    (germFam_congr hstart hf0.symm) 1) hg1.symm

end GoldbachBoundaries.HInf.MixProof
