import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.graphInt_eq_of_separating
import PrimePairNB.HInf.Fill.graphInt_line
import PrimePairNB.HInf.Fill.hasDerivAt_Pth
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.isSeparating_line
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-!
# `Dth_eq`, `Dth_eq_G`

On `2 < Re v < 3` a line separates and `P^θ = P` on it, so (K3) applies. `Dth_eq_G` extends this to `σ > 2` by the
identity theorem.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `D^θ = D` on `2 < Re v < 3`. -/
theorem Dth_eq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) (h3 : v.re < 3) : Dth k κ v = D v := by
  have hVt : v ∈ Vt top := by
    refine ⟨by linarith, lt_of_lt_of_le ?_ hK.three_le⟩
    have : ((v.re : ℝ) : EReal) < ((3 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr h3
    exact this.trans_eq (by norm_cast)
  have hv : v ∈ VInf top := (mem_Om_of_two_lt hZ1 (κ := κ) hVt h2).1
  set c : ℝ := v.re / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c < v.re - 1 := by rw [hc]; linarith
  rw [Dth_eq_graphInt hZ1 hZ2 hZ3 hK hv (isSeparating_line hZ1 κ hc1 hc2), graphInt_line,
    hK.mb v h2 h3 c hc1 hc2]
  have hpt : ∀ y : ℝ, pairIntegrand k κ v ((c : ℂ) + (y : ℂ) * I) =
      k ((c : ℂ) + (y : ℂ) * I) v * P ((c : ℂ) + (y : ℂ) * I) * P (v - ((c : ℂ) + (y : ℂ) * I)) := by
    intro y
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    unfold pairIntegrand
    rw [Pth_eq_P κ (by rw [hre]; exact hc1), Pth_eq_P κ (by rw [sub_re, hre]; linarith)]
  simp only [VerticalIntegral', VerticalIntegral, hpt]

/-- `D^θ = G` on all of `σ > 2`, by the identity theorem from `Dth_eq` (`ThmA.G_differentiableOn`). -/
theorem Dth_eq_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) :
    Dth kerG κ v = G v := by
  have hK := isPinchKernel_G hZ6
  set a : ℝ := (2 + min v.re 3) / 2 with ha
  have hm1 : 2 < min v.re 3 := lt_min h2 (by norm_num)
  have hm2 : min v.re 3 ≤ v.re := min_le_left _ _
  have hm3 : min v.re 3 ≤ 3 := min_le_right _ _
  have ha2 : 2 < a := by rw [ha]; linarith
  have ha3 : a < 3 := by rw [ha]; linarith
  have hav : a < v.re := by rw [ha]; linarith
  have hOpen : IsOpen (halfPlane a) := isOpen_lt continuous_const Complex.continuous_re
  have hsub : halfPlane a ⊆ Om κ ⊤ := fun z hz => by
    have hz' : a < z.re := hz
    exact mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ (by linarith)
  have hD : AnalyticOnNhd ℂ (Dth kerG κ) (halfPlane a) :=
    (Dth_analyticOn hZ1 hZ2 hZ3 hK κ).mono hsub
  have hG : AnalyticOnNhd ℂ G (halfPlane a) :=
    (ThmA.G_differentiableOn ha2).analyticOnNhd hOpen
  have hconn : IsPreconnected (halfPlane a) := (convex_halfSpace_re_gt a).isPreconnected
  set z₀ : ℂ := (((a + 3) / 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (a + 3) / 2 := by rw [hz₀]; exact Complex.ofReal_re _
  have hz₀mem : z₀ ∈ halfPlane a := by
    show a < z₀.re
    rw [hz₀re]; linarith
  have hstrip : {z : ℂ | 2 < z.re ∧ z.re < 3} ∈ 𝓝 z₀ := by
    refine ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ?_
    constructor
    · show 2 < z₀.re
      rw [hz₀re]; linarith
    · show z₀.re < 3
      rw [hz₀re]; linarith
  have hev : Dth kerG κ =ᶠ[𝓝 z₀] G := by
    filter_upwards [hstrip] with z hz
    exact Dth_eq hZ1 hZ2 hZ3 hK κ hz.1 hz.2
  exact hD.eqOn_of_preconnected_of_eventuallyEq hG hconn hz₀mem hev hav

end GoldbachBoundaries.HInf.Fill

