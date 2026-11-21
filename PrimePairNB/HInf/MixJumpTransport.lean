import PrimePairNB.HInf.MixLocalAssembly
import PrimePairNB.HInf.MixGermConst
import PrimePairNB.HInf.Fill.jump_line_transport
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- One east-to-west step. The analytic correction arriving from the east
continues across the disc; only the two logarithms change on its west side. -/
lemma local_jump_step (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
     (hK : IsPinchKernel kerG ⊤ G)
    {m κ p : ℝ} (hm : m < κ) (hp : κ < p)
    (hmg : IsGenericSlope m) (hpg : IsGenericSlope p)
    {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt ⊤) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf ⊤ ∧
      (∀ z ∈ ball x r, z ∈ Pinch → z = x) ∧
      ∀ (t : ℝ), 0 < t → ‖(t : ℂ) * slantDir κ‖ < r →
      ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Vt ⊤) →
      (DthMix p =ᶠ[𝓝 (x + (t : ℂ) * slantDir κ)] fun v => DthMix m v + g v) →
      DthMix p =ᶠ[𝓝 (x - (t : ℂ) * slantDir κ)] fun v => DthMix m v + g v + McMix x v := by
  obtain ⟨rm, hrm, hVm, hOm, Hm, hHm, hem⟩ := local_model hZ1 hZ2 hZ3 hK hmg hx hxV
  obtain ⟨rp, hrp, hVp, hOp, Hp, hHp, hep⟩ := local_model hZ1 hZ2 hZ3 hK hpg hx hxV
  let r := min rm rp
  have hr : 0 < r := lt_min hrm hrp
  have hbm : ball x r ⊆ ball x rm := ball_subset_ball (min_le_left _ _)
  have hbp : ball x r ⊆ ball x rp := ball_subset_ball (min_le_right _ _)
  have hiso : ∀ z ∈ ball x r, z ∈ Pinch → z = x := by
    intro z hz hzX
    have hzM : z ∈ rayW m x := by
      by_contra hn
      exact (hOm ⟨hbm hz, hn⟩).2 (mem_iUnion₂.mpr ⟨z, hzX, 0, le_rfl, by simp⟩)
    have hzP : z ∈ rayW p x := by
      by_contra hn
      exact (hOp ⟨hbp hz, hn⟩).2 (mem_iUnion₂.mpr ⟨z, hzX, 0, le_rfl, by simp⟩)
    obtain ⟨s, hs, he⟩ := hzM
    obtain ⟨u, hu, he'⟩ := hzP
    have hr' := congrArg Complex.re (he.symm.trans he')
    have hi' := congrArg Complex.im (he.symm.trans he')
    simp [slantDir] at hr' hi'
    have hsu : s = u := by linarith
    have hs0 : s = 0 := by
      rw [← hsu] at hi'
      have hh : s * (p - m) = 0 := by nlinarith
      exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt (sub_pos.mpr (hm.trans hp)))
    simpa [hs0] using he
  refine ⟨r, hr, hbm.trans hVm, hiso, ?_⟩
  intro t ht htr g hg he
  let e := x + (t : ℂ) * slantDir κ
  let w := x - (t : ℂ) * slantDir κ
  have heB : e ∈ ball x r := by simpa [e, mem_ball, dist_eq_norm] using htr
  have hwB : w ∈ ball x r := by simpa [w, mem_ball, dist_eq_norm, sub_sub_cancel_left] using htr
  have heM : e ∉ rayW m x := line_not_ray (ne_of_gt ht) (ne_of_lt hm)
  have heP : e ∉ rayW p x := line_not_ray (ne_of_gt ht) (ne_of_gt hp)
  have hwM : w ∉ rayW m x := by
    simpa [w, sub_eq_add_neg, ← neg_mul] using line_not_ray (x := x) (neg_ne_zero.mpr (ne_of_gt ht)) (ne_of_lt hm)
  have hwP : w ∉ rayW p x := by
    simpa [w, sub_eq_add_neg, ← neg_mul] using line_not_ray (x := x) (neg_ne_zero.mpr (ne_of_gt ht)) (ne_of_gt hp)
  have hmodel (z : ℂ) (hzB : z ∈ ball x r) (hzM : z ∉ rayW m x) (hzP : z ∉ rayW p x) :
      (DthMix m =ᶠ[𝓝 z] fun v => logK m (v - x) * XcMix x v + Hm v) ∧
      (DthMix p =ᶠ[𝓝 z] fun v => logK p (v - x) * XcMix x v + Hp v) := by
    have hmO := (isOpen_Om hZ1 m ⊤).mem_nhds (hOm ⟨hbm hzB, hzM⟩)
    have hpO := (isOpen_Om hZ1 p ⊤).mem_nhds (hOp ⟨hbp hzB, hzP⟩)
    have hnb := isOpen_ball.mem_nhds hzB
    constructor
    · filter_upwards [hnb, hmO] with v hvB hvO
      exact hem v ⟨hbm hvB, fun hvR => hvO.2 (mem_iUnion₂.mpr ⟨x, hx.1, hvR⟩)⟩
    · filter_upwards [hnb, hpO] with v hvB hvO
      exact hep v ⟨hbp hvB, fun hvR => hvO.2 (mem_iUnion₂.mpr ⟨x, hx.1, hvR⟩)⟩
  have hlogE : (fun v => logK p (v - x)) =ᶠ[𝓝 e] fun v => logK m (v - x) + 0 := by
    apply logK_germ heM heP
    simp only [e, add_sub_cancel_left, logK_east p κ ht, logK_east m κ ht, add_zero]
  have hHE : (fun v => Hp v - Hm v) =ᶠ[𝓝 e] g := by
    filter_upwards [he, (hmodel e heB heM heP).1, (hmodel e heB heM heP).2, hlogE] with v hv hvm hvp hvl
    simp only [add_zero] at hvl
    rw [hvl] at hvp
    linear_combination hv + hvm - hvp
  have hHg := ((hHp.mono hbp).sub (hHm.mono hbm)).eqOn_of_preconnected_of_eventuallyEq
    (hg.mono (fun v hv => (hVm (hbm hv)).1)) (convex_ball x r).isPreconnected heB hHE
  have hlogW : (fun v => logK p (v - x)) =ᶠ[𝓝 w] fun v => logK m (v - x) + 2 * (Real.pi : ℂ) * I := by
    apply logK_germ hwM hwP
    have hh := logK_west hm hp ht
    change logK p (w - x) = logK m (w - x) + _
    have hwx : w - x = -((t : ℂ) * slantDir κ) := by dsimp [w]; ring
    rw [hwx]
    linear_combination hh
  filter_upwards [(hmodel w hwB hwM hwP).1, (hmodel w hwB hwM hwP).2,
    hlogW, isOpen_ball.mem_nhds hwB] with v hvm hvp hvl hvB
  have hh := hHg hvB
  change Hp v - Hm v = g v at hh
  dsimp only [McMix]
  rw [hvp, hvm, hvl]
  linear_combination hh

end GoldbachBoundaries.HInf.MixProof
