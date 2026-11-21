import PrimePairNB.HInf.Fill.local_model
import PrimePairNB.HInf.Fill.germ_const
import PrimePairNB.HInf.Fill.jump_line_log
import PrimePairNB.HInf.Fill.finite_inter_pinch

/-! Analytic transport along a connected set, and across one logarithmic point. -/
noncomputable section
open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma analytic_germ_transport {U S : Set ℂ} {a b : ℂ} {f g : ℂ → ℂ}
    (ho : IsOpen U) (hc : IsPreconnected S) (hs : S ⊆ U) (ha : a ∈ S) (hb : b ∈ S)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (he : f =ᶠ[𝓝 b] g) :
    f =ᶠ[𝓝 a] g := by
  let C := connectedComponentIn U a
  have hC : S ⊆ C := hc.subset_connectedComponentIn ha hs
  have hsub : C ⊆ U := connectedComponentIn_subset U a
  have heq := (hf.mono hsub).eqOn_of_preconnected_of_eventuallyEq (hg.mono hsub)
    isPreconnected_connectedComponentIn (hC hb) he
  exact Filter.eventuallyEq_of_mem
    (ho.connectedComponentIn.mem_nhds (mem_connectedComponentIn (hs ha))) heq

lemma line_not_ray {x : ℂ} {κ σ t : ℝ} (ht : t ≠ 0) (hσ : σ ≠ κ) :
    x + (t : ℂ) * slantDir κ ∉ rayW σ x := by
  rintro ⟨s, hs, he⟩
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp [slantDir] at hr hi
  have hts : t = -s := by linarith
  have heq : t * (κ - σ) = 0 := by rw [hts] at hi ⊢; nlinarith
  exact hσ (by rcases mul_eq_zero.mp heq with h | h; exact False.elim (ht h); linarith)

/-- One east-to-west step. The analytic correction arriving from the east
continues across the disc; only the two logarithms change on its west side. -/
lemma local_jump_step (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D)
    {m κ p : ℝ} (hm : m < κ) (hp : κ < p)
    (hmg : IsGenericSlope m) (hpg : IsGenericSlope p)
    {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf top ∧
      (∀ z ∈ ball x r, z ∈ Pinch → z = x) ∧
      ∀ (t : ℝ), 0 < t → ‖(t : ℂ) * slantDir κ‖ < r →
      ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Vt top) →
      (Dth k p =ᶠ[𝓝 (x + (t : ℂ) * slantDir κ)] fun v => Dth k m v + g v) →
      Dth k p =ᶠ[𝓝 (x - (t : ℂ) * slantDir κ)] fun v => Dth k m v + g v + Mc k x v := by
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
      (Dth k m =ᶠ[𝓝 z] fun v => logK m (v - x) * Xc k x v + Hm v) ∧
      (Dth k p =ᶠ[𝓝 z] fun v => logK p (v - x) * Xc k x v + Hp v) := by
    have hmO := (isOpen_Om hZ1 m top).mem_nhds (hOm ⟨hbm hzB, hzM⟩)
    have hpO := (isOpen_Om hZ1 p top).mem_nhds (hOp ⟨hbp hzB, hzP⟩)
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
  dsimp only [Mc]
  rw [hvp, hvm, hvl]
  linear_combination hh

end GoldbachBoundaries.HInf.Fill
