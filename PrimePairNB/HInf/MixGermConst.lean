import PrimePairNB.HInf.MixNormalization
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

private theorem east_mem_common  {v : ℂ} {κ₁ κ₂ : ℝ}
    (h : κ₁ ≤ κ₂) (hmem : ∀ κ ∈ Icc κ₁ κ₂, v ∈ Om κ ⊤)
    {t : ℝ} (ht : 0 ≤ t) (hV : v + (t : ℂ) * slantDir κ₁ ∈ Vt ⊤)
    {σ : ℝ} (hσ : σ ∈ Icc κ₁ κ₂) :
    v + (t : ℂ) * slantDir κ₁ ∈ Om σ ⊤ := by
  have hv := hmem κ₁ ⟨le_rfl, h⟩
  by_cases ht0 : t = 0
  · simpa [ht0] using hmem σ hσ
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  refine ⟨⟨hV, ?_⟩, ?_⟩
  · have hre : (v + (t : ℂ) * slantDir κ₁).re = v.re + t := by simp [slantDir]
    rw [hre]
    linarith [hv.1.2]
  · simp only [mem_iUnion, not_exists]
    rintro x hx ⟨s, hs, heq⟩
    let q : ℝ := (t * κ₁ + s * σ) / (t + s)
    have hts : 0 < t + s := by linarith
    have hq : q ∈ Icc κ₁ κ₂ := by
      constructor
      · apply (le_div_iff₀ hts).mpr
        nlinarith [hσ.1]
      · apply (div_le_iff₀ hts).mpr
        nlinarith [hσ.2]
    have hmul : q * (t + s) = t * κ₁ + s * σ := div_mul_cancel₀ _ (ne_of_gt hts)
    apply (hmem q hq).2
    refine mem_iUnion₂.mpr ⟨x, hx, t + s, le_of_lt hts, ?_⟩
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    simp [slantDir] at hr hi
    apply Complex.ext <;> simp [slantDir] <;> nlinarith

/-- If `v₁ ∈ Ω_κ` for every `κ` in an interval, the germ of `D^κ` at `v₁` is constant on it. -/
theorem germ_const (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) {v₁ : ℂ} {κ₁ κ₂ : ℝ} (h : κ₁ ≤ κ₂) (hmem : ∀ κ ∈ Icc κ₁ κ₂, v₁ ∈ Om κ ⊤) :
    DthMix κ₂ =ᶠ[𝓝 v₁] DthMix κ₁ := by
  have hv₁ := hmem κ₁ ⟨le_rfl, h⟩
  have hv₂ := hmem κ₂ ⟨h, le_rfl⟩
  have heq {z : ℂ} (hz2 : 2 < z.re) (hz3 : z.re < 3) : DthMix κ₂ z = DthMix κ₁ z :=
    (Dth_eq hZ1 hZ2 hZ3 hK κ₂ hz2).trans (Dth_eq hZ1 hZ2 hZ3 hK κ₁ hz2).symm
  have hstrip {z : ℂ} (hz2 : 2 < z.re) (hz3 : z.re < 3) : DthMix κ₂ =ᶠ[𝓝 z] DthMix κ₁ := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (show 2 < z.re ∧ z.re < 3 from ⟨hz2, hz3⟩)] with w hw
    exact heq hw.1 hw.2
  by_cases hv2 : 2 < v₁.re
  · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hv2] with z hz
    exact (Dth_eq hZ1 hZ2 hZ3 hK κ₂ hz).trans (Dth_eq hZ1 hZ2 hZ3 hK κ₁ hz).symm
  · have hvle : v₁.re ≤ 2 := le_of_not_gt hv2
    let T : ℝ := 5 / 2 - v₁.re
    have hT : 0 ≤ T := by dsimp [T]; linarith
    let p : ℝ → ℂ := fun t => v₁ + (t : ℂ) * slantDir κ₁
    let U : Set ℂ := Om κ₁ ⊤ ∩ Om κ₂ ⊤
    let C : Set ℂ := connectedComponentIn U v₁
    have hUo : IsOpen U := (isOpen_Om hZ1 κ₁ ⊤).inter (isOpen_Om hZ1 κ₂ ⊤)
    have h52 : (((5 / 2 : ℝ)) : EReal) < ⊤ := lt_of_lt_of_le (by
      have hh : (((5 / 2 : ℝ)) : EReal) < ((3 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by norm_num)
      exact hh.trans_eq (by norm_cast)) hK.three_le
    have hp : p '' Icc 0 T ⊆ U := by
      rintro _ ⟨t, ht, rfl⟩
      have hV : p t ∈ Vt ⊤ := by
        have hre : (p t).re = v₁.re + t := by simp [p, slantDir]
        refine ⟨?_, ?_⟩
        · rw [hre]; linarith [hv₁.1.1.1, ht.1]
        · rw [hre]
          have htT : t ≤ 5 / 2 - v₁.re := ht.2
          apply lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (show v₁.re + t ≤ 5 / 2 from by linarith)) h52
      exact ⟨east_mem_common h hmem ht.1 hV ⟨le_rfl, h⟩,
        east_mem_common h hmem ht.1 hV ⟨h, le_rfl⟩⟩
    have hpc : IsPreconnected (p '' Icc 0 T) := isPreconnected_Icc.image p (by fun_prop)
    have hvp : v₁ ∈ p '' Icc 0 T := ⟨0, ⟨le_rfl, hT⟩, by simp [p]⟩
    have hC : p '' Icc 0 T ⊆ C := hpc.subset_connectedComponentIn hvp hp
    have hpT : p T ∈ C := hC ⟨T, ⟨hT, le_rfl⟩, rfl⟩
    have hCre : (p T).re = 5 / 2 := by simp [p, T, slantDir]
    have hCsub : C ⊆ U := connectedComponentIn_subset U v₁
    have hf := (Dth_analyticOn hZ1 hZ2 hZ3 hK κ₂).mono (fun z hz => (hCsub hz).2)
    have hg := (Dth_analyticOn hZ1 hZ2 hZ3 hK κ₁).mono (fun z hz => (hCsub hz).1)
    have hE := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_connectedComponentIn hpT
      (hstrip (by rw [hCre]; norm_num) (by rw [hCre]; norm_num))
    exact Filter.eventuallyEq_of_mem (hUo.connectedComponentIn.mem_nhds (mem_connectedComponentIn ⟨hv₁, hv₂⟩)) hE

end GoldbachBoundaries.HInf.MixProof
