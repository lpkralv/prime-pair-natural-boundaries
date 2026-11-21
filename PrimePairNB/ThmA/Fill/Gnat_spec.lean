import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.Gb_spec
import PrimePairNB.ThmA.Fill.cuts_locallyFinite
import PrimePairNB.ThmA.Fill.isPreconnected_Omega_inter

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.ThmA

lemma F_bOf_mem {s : ℂ} (hs : s ∈ HH) :
    bOf s ∈ Ioo (1 / 2 : ℝ) 1 ∧ 2 * bOf s < s.re := by
  have hs' : (1 : ℝ) < s.re := hs
  unfold bOf
  constructor
  · constructor
    · have := lt_min (by linarith : (1 / 2 : ℝ) < s.re / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      linarith
    · have := min_le_right (s.re / 2) (1 : ℝ)
      linarith
  · have := min_le_left (s.re / 2) (1 : ℝ)
    linarith

lemma F_Gb_compat (hRH : RiemannHypothesis) (κ : ℝ) {b c : ℝ}
    (hb : b ∈ Ioo (1 / 2 : ℝ) 1) (hc : c ∈ Ioo (1 / 2 : ℝ) 1) :
    EqOn (Gb κ b) (Gb κ c) (Omega κ ∩ halfPlane (2 * max b c)) := by
  have hbm : Omega κ ∩ halfPlane (2 * max b c) ⊆ Omega κ ∩ halfPlane (2 * b) := by
    rintro s ⟨hs, hsc⟩
    refine ⟨hs, ?_⟩
    change 2 * b < s.re
    have : 2 * max b c < s.re := hsc
    linarith [le_max_left b c]
  have hcm : Omega κ ∩ halfPlane (2 * max b c) ⊆ Omega κ ∩ halfPlane (2 * c) := by
    rintro s ⟨hs, hsc⟩
    refine ⟨hs, ?_⟩
    change 2 * c < s.re
    have : 2 * max b c < s.re := hsc
    linarith [le_max_right b c]
  have hm : max b c < 1 := max_lt hb.2 hc.2
  have h3 : (3 : ℂ) ∈ Omega κ ∩ halfPlane (2 * max b c) := by
    refine ⟨halfPlane_two_subset_Omega κ (by norm_num [halfPlane]), ?_⟩
    change 2 * max b c < (3 : ℂ).re
    norm_num
    linarith
  apply ((Gb_spec hRH κ hb).1.mono hbm).eqOn_of_preconnected_of_eventuallyEq
    ((Gb_spec hRH κ hc).1.mono hcm) (isPreconnected_Omega_inter κ hm) h3
  filter_upwards [(isOpen_halfPlane 2).mem_nhds (show (3 : ℂ) ∈ halfPlane 2 by norm_num [halfPlane])]
    with s hs
  exact ((Gb_spec hRH κ hb).2 hs).trans ((Gb_spec hRH κ hc).2 hs).symm

/-- **the principal-sheet proposition.** `G^♮` is holomorphic on `Ω_ℍ`, equals `G` on `σ > 2`, and equals
`G^♮_b` on `Ω_ℍ ∩ R_b` for every `b ∈ (1/2, 1)`. Under RH, any slope.

Sketch. For `b < b'`, `Gb b` and `Gb b'` are holomorphic on the connected
`Ω_ℍ ∩ R_{b'}` (`isPreconnected_Omega_inter`) and agree with `G` on `σ > 2`, so agree there
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`). For `s ∈ ℍ`, `bOf s ∈ (1/2, 3/4]` and
`2·bOf s < σ`; `bOf` is continuous, so near `s₀ ∈ Ω_ℍ`, `Gnat = Gb (bOf s₀)` (both points lie in
`R_{max}`), which is holomorphic at `s₀`. -/
theorem Gnat_spec (hRH : RiemannHypothesis) (κ : ℝ) :
    AnalyticOnNhd ℂ (Gnat κ) (Omega κ) ∧ EqOn (Gnat κ) G (halfPlane 2) ∧
      ∀ b ∈ Ioo (1 / 2 : ℝ) 1, EqOn (Gnat κ) (Gb κ b) (Omega κ ∩ halfPlane (2 * b)) := by
  have heq : ∀ b ∈ Ioo (1 / 2 : ℝ) 1,
      EqOn (Gnat κ) (Gb κ b) (Omega κ ∩ halfPlane (2 * b)) := by
    intro b hb s hs
    have hbo := F_bOf_mem (Omega_subset hs.1).1
    apply F_Gb_compat hRH κ hbo.1 hb
    refine ⟨hs.1, ?_⟩
    change 2 * max (bOf s) b < s.re
    rcases le_total (bOf s) b with h | h
    · rw [max_eq_right h]
      exact hs.2
    · rw [max_eq_left h]
      exact hbo.2
  refine ⟨?_, ?_, heq⟩
  · intro s hs
    have hbo := F_bOf_mem (Omega_subset hs).1
    have hU : IsOpen (Omega κ ∩ halfPlane (2 * bOf s)) :=
      (cuts_locallyFinite κ).2.inter (isOpen_halfPlane _)
    have hsU : s ∈ Omega κ ∩ halfPlane (2 * bOf s) := ⟨hs, hbo.2⟩
    exact ((Gb_spec hRH κ hbo.1).1 s hsU).congr
      (heq (bOf s) hbo.1 |>.eventuallyEq_of_mem (hU.mem_nhds hsU)).symm
  · intro s hs
    have hsH : s ∈ HH := by change 1 < s.re; have : 2 < s.re := hs; linarith
    exact (Gb_spec hRH κ (F_bOf_mem hsH).1).2 hs

end GoldbachBoundaries.ThmA
