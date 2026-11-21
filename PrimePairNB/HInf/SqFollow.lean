import PrimePairNB.HInf.SqFollowTransport
import PrimePairNB.HInf.MixFollowCommon

/-! Continuation and near-line non-vacuity for the prime-square series. -/
noncomputable section
open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf

namespace SqFollow

lemma continuesAlong_DSq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (hγ : ∀ t, γ t ∈ VInf ⊤ \ Pinch)
    (h0 : 2 < (γ 0).re) : ContinuesAlong DSq γ := by
  have hstart : GermFam kSq ⊤ 0 (γ 0) DSq := by
    refine ⟨0, mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ h0,
      0, zero_mem _, ?_⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0] with v hv
    simp [Dth_eq_Sq hZ1 hZ2 hZ3 hZ6 0 hv]
  obtain ⟨f, hf, hf0, -⟩ := ThmA.exists_continuationAlong_of_uniform
    (uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_Sq_top hZ6) 0) hγ hstart
  exact ⟨f, hf, hf0⟩

lemma hh_to_vinf (hH : Hinf) (hZ1 : Z1) {v : ℂ} (hv : v ∈ HH \ catG) :
    v ∈ VInf ⊤ \ Pinch := by
  have hre : 1 < v.re := hv.1
  rw [VInf_eq_of_Hinf hZ1 hH]
  exact ⟨⟨hre, EReal.coe_lt_top _⟩, fun hp => hv.2 (mem_catG_iff.mpr ⟨hre, hp⟩)⟩

lemma exists_admSqV_iff (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {v : ℂ} : (∃ g : ℂ → ℂ, AdmSqV g v) ↔ v ∈ HH \ catG :=
  Follow.exists_adm_iff (fun _ hγ h0 => continuesAlong_DSq hZ1 hZ2 hZ3 hZ6
    (fun t => hh_to_vinf hH hZ1 (hγ t)) h0)

end SqFollow

/-- Sq continuation in the unbounded uniform-family domain, in the original coordinate. -/
theorem continuesAlong_Sq_vinf (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (hγ : ∀ t, 2 * γ t ∈ VInf ⊤ \ Pinch)
    (h0 : 1 < (γ 0).re) : ContinuesAlong SqSer γ := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => 2 * γ t, by fun_prop⟩
  have hδ0 : 2 < (δ 0).re := by change 2 < (2 * γ 0).re; simp; linarith
  obtain ⟨f, hf, hf0⟩ := SqFollow.continuesAlong_DSq hZ1 hZ2 hZ3 hZ6 (γ := δ) hγ hδ0
  refine ⟨fun t s => f t (2 * s), ⟨fun t => ?_, fun t => ?_⟩, ?_⟩
  · simpa only [δ, ContinuousMap.coe_mk, SqFollow.half_double] using
      SqFollow.analyticAt_double (hf.analyticAt t)
  · filter_upwards [hf.locallyEq t] with t' ht'
    simpa only [δ, ContinuousMap.coe_mk, SqFollow.half_double] using
      SqFollow.eventuallyEq_double ht'
  · simpa only [δ, ContinuousMap.coe_mk, DSq, SqFollow.half_double] using
      SqFollow.eventuallyEq_double hf0

/-- Every path in the admissible region from the convergence half-plane admits continuation. -/
theorem continuesAlong_Sq (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (hγ : ∀ t, γ t ∈ Aff.twoL.HL \ catSq)
    (h0 : 1 < (γ 0).re) : ContinuesAlong SqSer γ := by
  apply continuesAlong_Sq_vinf hZ1 hZ2 hZ3 hZ6 (h0 := h0)
  intro t
  have ht := hγ t
  have hre : 1 / 2 < (γ t).re := by simpa only [twoL_HL, halfPlane, mem_ofPred_eq] using ht.1
  apply SqFollow.hh_to_vinf hH hZ1
  refine ⟨?_, ?_⟩
  · show 1 < (2 * γ t).re
    simp; linarith
  · intro hc
    exact ht.2 (mem_catSq_iff.mpr ⟨hre, (mem_catG_iff.mp hc).2⟩)

/-- Any continuation from the convergence half-plane has an admissible endpoint off the catalogue. -/
theorem every_path_Sq (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {γ : C(unitInterval, ℂ)}
    (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm SqSer γ g)
    (h1 : γ 1 ∉ catSq) : AdmSq g (γ 1) := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => 2 * γ t, by fun_prop⟩
  have hδ0 : 2 < (δ 0).re := by change 2 < (2 * γ 0).re; simp; linarith
  have hδ1 : δ 1 ∉ catG := by
    intro hc
    have hc' := mem_catG_iff.mp hc
    apply h1
    refine mem_catSq_iff.mpr ⟨?_, hc'.2⟩
    have hre : 1 < (2 * γ 1).re := hc'.1
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hre
    linarith
  have had : AdmSqV (fun v => g (v / 2)) (δ 1) :=
    Follow.every_path hH hZ1 (fun _ hs => DSq_analyticAt hs)
      (fun _ _ had => boundary_SqV hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 had)
      hδ0 (SqFollow.terminal_double hg) hδ1
  simpa only [δ, ContinuousMap.coe_mk, SqFollow.half_double] using SqFollow.admSq_of_admSqV had

/-- Exactly the points of the admissible region carry prime-square admissible germs. -/
theorem exists_admSq_iff (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {s₁ : ℂ} : (∃ g : ℂ → ℂ, AdmSq g s₁) ↔ s₁ ∈ Aff.twoL.HL \ catSq := by
  constructor
  · rintro ⟨g, γ, hγ, -, rfl, -⟩
    exact hγ 1
  · intro hs
    have hre : 1 / 2 < s₁.re := by simpa only [twoL_HL, halfPlane, mem_ofPred_eq] using hs.1
    have hv : 2 * s₁ ∈ HH \ catG := by
      refine ⟨?_, fun hc => hs.2 (mem_catSq_iff.mpr ⟨hre, (mem_catG_iff.mp hc).2⟩)⟩
      show 1 < (2 * s₁).re
      simp; linarith
    obtain ⟨g, hg⟩ := (SqFollow.exists_admSqV_iff hH hZ1 hZ2 hZ3 hZ6).mpr hv
    exact ⟨fun s => g (2 * s), by simpa only [SqFollow.half_double] using SqFollow.admSq_of_admSqV hg⟩

/-- Every disc centred on `Re s = 1/2` contains an admissible prime-square germ. -/
theorem exists_admSq_near (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∀ y : ℝ, ∀ r : ℝ, 0 < r → ∃ (s₁ : ℂ) (g : ℂ → ℂ),
      s₁ ∈ ball ((1/2 : ℂ) + (y : ℂ) * I) r ∧ AdmSq g s₁ := by
  intro y r hr
  obtain ⟨v, g, hv, hg⟩ := Follow.exists_adm_near
    (F := DSq) (fun _ hs => (SqFollow.exists_admSqV_iff hH hZ1 hZ2 hZ3 hZ6).mpr hs)
    (2 * y) (2 * r) (by linarith)
  refine ⟨v / 2, fun s => g (2 * s), ?_, SqFollow.admSq_of_admSqV hg⟩
  have he : (1 + ((2 * y : ℝ) : ℂ) * I) / 2 = (1/2 : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  rw [mem_ball, ← he, dist_sq_half]
  have hd : dist v (1 + ((2 * y : ℝ) : ℂ) * I) < 2 * r := hv
  linarith

end GoldbachBoundaries.HInf

