import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.Qcont_pole_split
import PrimePairNB.ThmA.Fill.exists_Eaux

set_option maxHeartbeats 1000000
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

private theorem D_Qcont_eq_Q {z : ℂ} (hz : z ∈ HH) : Qcont z = Q z := by
  rw [← (hasSum_Q_moebius_zeta hz).tsum_eq, Qcont]
  apply tsum_congr
  intro n
  simp [sigmaTerm, negLogDerivZeta, neg_div]

private theorem D_Eaux_deriv (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) :
    HasDerivAt Eaux (-Qcont z + 1 / (z - 1)) z := by
  obtain ⟨q, hq, hQ⟩ := Qcont_pole_split hRH (a := 1) (by simp [PoleSetQ])
  have hqh : AnalyticOnNhd ℂ q (halfPlane (1 / 2)) := by
    intro w hw
    apply hq w
    refine ⟨show 0 < w.re by have : 1 / 2 < w.re := hw; linarith, ?_⟩
    rintro ⟨hwS, hw1⟩
    have hm : w ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨hwS, hw⟩
    rw [(lem_Sigma_iv_proof hRH).1] at hm
    exact hw1 hm
  have heq : ∀ w ∈ HH, deriv Eaux w = -q w := by
    intro w hw
    have hw' : 1 < w.re := hw
    have hw0 : 0 < w.re := by linarith
    have hwhalf : w ∈ halfPlane (1 / 2) := by change 1 / 2 < w.re; linarith
    have hw1 : w ≠ 1 := by intro he; simp [he] at hw'
    have hwS : w ∉ PoleSetQ := by
      intro he
      have hm : w ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨he, hwhalf⟩
      rw [(lem_Sigma_iv_proof hRH).1] at hm
      exact hw1 hm
    have hsplit := hQ w hw0 hwS
    rw [sigmaRes_eq hasResidue_Qcont_one, D_Qcont_eq_Q hw] at hsplit
    have hlog : w - 1 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    have hp := (hasDerivAt_P hw).add (((hasDerivAt_id w).sub_const 1).clog hlog)
    have hloc : Eaux =ᶠ[𝓝 w] (fun w => P w + Complex.log (w - 1)) := by
      filter_upwards [(isOpen_halfPlane 1).mem_nhds hw] with t ht
      exact (Eaux_spec hRH).2 t ht
    rw [hloc.deriv_eq]
    calc
      _ = -Q w + 1 / (w - 1) := hp.deriv
      _ = -q w := by linear_combination -hsplit
  have heqall : EqOn (deriv Eaux) (fun w => -q w) (halfPlane (1 / 2)) := by
    apply (Eaux_spec hRH).1.deriv.eqOn_of_preconnected_of_eventuallyEq hqh.neg
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
      (show (2 : ℂ) ∈ halfPlane (1 / 2) by norm_num [halfPlane])
    filter_upwards [(isOpen_halfPlane 1).mem_nhds (show (2 : ℂ) ∈ HH by norm_num [halfPlane])]
      with w hw
    exact heq w hw
  have hzS : z ∉ PoleSetQ := by
    intro he
    have hm : z ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨he, hz⟩
    rw [(lem_Sigma_iv_proof hRH).1] at hm
    exact hz1 hm
  have hs := hQ z (by linarith : 0 < z.re) hzS
  rw [sigmaRes_eq hasResidue_Qcont_one] at hs
  have hd := ((Eaux_spec hRH).1 z hz).differentiableAt.hasDerivAt
  rw [heqall hz] at hd
  convert hd using 1
  linear_combination -hs

private theorem D_log_div_right {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x / y) + Complex.log y = Complex.log x := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hay := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have he : Complex.exp (Complex.log x - Complex.log y) = x / y := by
    rw [Complex.exp_sub, Complex.exp_log hx0, Complex.exp_log hy0]
  rw [← he, Complex.log_exp]
  · ring
  · simp only [sub_im, log_im]
    linarith
  · simp only [sub_im, log_im]
    linarith

private theorem D_log_upper {w : ℂ} (hw : 0 < w.im) :
    Complex.log w = Complex.log (-w) + (Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast
  ring

/-- **The slanted branch `P_v`** (a branch of `P`, equal to the Dirichlet series
on `Re z > 1`; its derivative is `-Q`; continuation from the `+` side).

Sketch. (1) `Log((z-1)/v) + Log v = Log(z-1)` for `Re z > 1`: `Re v = 1 > 0`, `Re(z-1) > 0`, so all
arguments lie in `(-π/2, π/2)` and `Complex.log_mul`/`arg` bookkeeping applies (any `κ`).
(2) `logAt v 1` is analytic where `(z-1)/v ∈ slitPlane` (`analyticAt_clog`), derivative `1/(z-1)`;
`Eaux' = -Qcont + 1/(z-1)` on `H_{1/2} ∖ {1}` (identity theorem from `ℍ`, `Eaux_spec`). (3) If
`(z₀ - 1)/v ∉ (-∞, 0]` take `F = Pv`; otherwise `(z₀-1)/v < 0` and take
`F z = Eaux z - (Log(-(z-1)/v) + iπ + Log v)` (`Log(-w) + iπ = Log w` for `Im w > 0`). -/
theorem Pv_spec (hRH : RiemannHypothesis) (κ : ℝ) :
    (∀ z ∈ HH, Pv κ z = P z) ∧
    (∀ z : ℂ, 1 / 2 < z.re → (z - 1) / slantDir κ ∈ slitPlane →
      AnalyticAt ℂ (Pv κ) z ∧ HasDerivAt (Pv κ) (-Qcont z) z) ∧
    (∀ z₀ : ℂ, 1 / 2 < z₀.re → z₀ ≠ 1 → ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball z₀ r) ∧
        ∀ z ∈ ball z₀ r, 0 < ((z - 1) / slantDir κ).im → F z = Pv κ z) := by
  have hv := slantDir_ne_zero κ
  have hlin : ∀ z : ℂ, AnalyticAt ℂ (fun z => (z - 1) / slantDir κ) z := by
    intro z
    exact (analyticAt_id.sub analyticAt_const).div analyticAt_const hv
  have han : ∀ z : ℂ, 1 / 2 < z.re → (z - 1) / slantDir κ ∈ slitPlane →
      AnalyticAt ℂ (Pv κ) z ∧ HasDerivAt (Pv κ) (-Qcont z) z := by
    intro z hz hsl
    have hz1 : z ≠ 1 := by intro he; simp [he, Complex.slitPlane] at hsl
    have hz0 := sub_ne_zero.mpr hz1
    have ha : AnalyticAt ℂ (Pv κ) z := by
      exact ((Eaux_spec hRH).1 z hz).sub
        (((analyticAt_clog hsl).comp (f := fun z : ℂ => (z - 1) / slantDir κ) (hlin z)).add analyticAt_const)
    have hd := (D_Eaux_deriv hRH hz hz1).sub
      (((((hasDerivAt_id z).sub_const 1).div_const (slantDir κ)).clog hsl).add_const
        (Complex.log (slantDir κ)))
    refine ⟨ha, ?_⟩
    convert hd using 1
    · rfl
    · dsimp
      field_simp
      ring
  refine ⟨?_, han, ?_⟩
  · intro z hz
    have hz' : 1 < z.re := hz
    have hvre : 0 < (slantDir κ).re := by simp [slantDir]
    have hzre : 0 < (z - 1).re := by simp; linarith
    rw [Pv, logAt, (Eaux_spec hRH).2 z hz, D_log_div_right hzre hvre]
    ring
  · intro z₀ hz₀ hz₁
    by_cases hsl : (z₀ - 1) / slantDir κ ∈ slitPlane
    · obtain ⟨r, hr, hrF⟩ := Metric.eventually_nhds_iff_ball.mp (han z₀ hz₀ hsl).1.eventually_analyticAt
      exact ⟨r, hr, Pv κ, fun z hz => hrF z (mem_ball.mp hz), fun _ _ _ => rfl⟩
    · have hw0 : (z₀ - 1) / slantDir κ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hz₁) hv
      have hwre : ((z₀ - 1) / slantDir κ).re < 0 := by
        rw [mem_slitPlane_iff] at hsl
        push_neg at hsl
        have hne : ((z₀ - 1) / slantDir κ).re ≠ 0 := by
          intro he
          apply hw0
          apply Complex.ext <;> simp [he, hsl.2]
        exact lt_of_le_of_ne hsl.1 hne
      let F : ℂ → ℂ := fun z => Eaux z -
        (Complex.log (-((z - 1) / slantDir κ)) + (Real.pi : ℂ) * I + Complex.log (slantDir κ))
      have hF : AnalyticAt ℂ F z₀ := by
        have hneg : -((z₀ - 1) / slantDir κ) ∈ slitPlane :=
          mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
        exact ((Eaux_spec hRH).1 z₀ hz₀).sub
          ((((analyticAt_clog hneg).comp (f := fun z : ℂ => -((z - 1) / slantDir κ)) (hlin z₀).neg).add analyticAt_const).add analyticAt_const)
      obtain ⟨r, hr, hrF⟩ := Metric.eventually_nhds_iff_ball.mp hF.eventually_analyticAt
      refine ⟨r, hr, F, fun z hz => hrF z (mem_ball.mp hz), ?_⟩
      intro z hz him
      dsimp [F, Pv, logAt]
      rw [D_log_upper him]

end GoldbachBoundaries.ThmA
