import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.FCommon
import PrimePairNB.ThmA.Fill.Dc_eq_diag
import PrimePairNB.ThmA.Fill.cauchyEnd

noncomputable section
set_option pp.proofs false
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

open FCauchy FEndpoint in
/-- **Local form of `𝒟` at `2`** (the local model, case `α = 2`: `𝒟 = +Γ(s)J_{11}Log_2 + hol`).
No RH.

Sketch. `Dc_eq_diag`; split at `w* ∈ (0, 1-b)`; on `[w*, 2(1-b)]` holomorphic near `ε = 0`. On
`[0, w*]`, `phiD w = f w` with `f(w) = segInt (u ↦ Γ(1-uv)Γ(1-(w-u)v)) 0 w`, holomorphic near
`[0, w*] ∪ ball 0 ρ`; `cauchyEnd` gives `-v f(-ε) Log ε + hol`, and `-v f(-ε) = Γ(s)J_{11}(s)` for
`s = 2 + εv` (expand `segInt` in both; substitute `τ ↦ 1-τ`). -/
theorem Dc_local_two (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 2 r) ∧
      ∀ s ∈ ball (2 : ℂ) r, (s - 2) / slantDir κ ∈ slitPlane →
        Dc κ b s = Gamma s * J 1 1 s * logAt (slantDir κ) 2 s + H s := by
  have hbpos := hb.1
  set v := slantDir κ with hv
  have hv0 : v ≠ 0 := slantDir_ne_zero κ
  have hvre : v.re = 1 := by simp [hv, slantDir]
  have hvn : 1 ≤ ‖v‖ := by simpa [hvre] using abs_re_le_norm v
  have hdiv : ∀ z : ℂ, ‖z / v‖ ≤ ‖z‖ := fun z => by
    rw [norm_div]; exact div_le_self (norm_nonneg _) hvn
  set c : ℝ := (1 - b) / 2 with hc
  have hc0 : 0 < c := by dsimp [c]; linarith [hb.2]
  have hcb : c < 1 - b := by dsimp [c]; linarith [hb.2]
  set K : ℝ := 1 + |κ| with hK
  have hK0 : 0 < K := by positivity
  set η : ℝ := b / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  have hηK : η + η * |κ| = b / 4 := by
    calc η + η * |κ| = η * K := by rw [hK]; ring
         _ = b / 4 := by rw [hη]; field_simp [hK0.ne']
  set ρ : ℝ := min η (c / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hη0 (by positivity)
  have hρη : ρ ≤ η := min_le_left _ _
  have hρc : ρ ≤ c / 2 := min_le_right _ _
  let U : Set ℂ := {z | z.re < c + η} ∩ {z | -η < z.im} ∩ {z | z.im < η}
  have hU : IsOpen U :=
    ((isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt continuous_const continuous_im)).inter (isOpen_lt continuous_im continuous_const)
  have hUc : Convex ℝ U :=
    ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_gt _)).inter (convex_halfSpace_im_lt _)
  have hball : ball (0 : ℂ) ρ ⊆ U := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_le_norm z) hz)
    have him := abs_lt.mp (lt_of_le_of_lt (abs_im_le_norm z) hz)
    exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, by dsimp; linarith⟩
  have hsegU : ∀ u ∈ Icc (0 : ℝ) c, (u : ℂ) ∈ U := by
    intro u hu
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [mem_ofPred_eq, ofReal_re, ofReal_im] <;>
      linarith [hu.2]
  let g : ℂ → ℂ := fun z => segInt (kG v z) 0 z
  have hgW : DifferentiableOn ℂ g {z : ℂ | (z * v).re < 1} :=
    segGamma_differentiableOn (p := fun _ => (0 : ℂ)) (q := fun z => z)
      (differentiable_const _) differentiable_id (isOpen_lt (by fun_prop) continuous_const)
      (fun _ _ => by simp) (fun _ hz => hz) (fun _ hz => by simpa using hz)
      (fun _ _ => by simp)
  have hUW : U ⊆ {z : ℂ | (z * v).re < 1} := by
    rintro z ⟨⟨hzr, hzi⟩, hzi'⟩
    have he : (z * v).re = z.re - z.im * κ := by simp [hv, slantDir]
    have hi : |z.im * κ| ≤ η * |κ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_lt.mpr ⟨hzi, hzi'⟩).le (abs_nonneg _)
    have hi' := abs_le.mp hi
    change (z * v).re < 1
    rw [he]
    dsimp only [mem_ofPred_eq] at hzr
    linarith [hb.1, hb.2, hc, hi'.1]
  obtain ⟨H0, hH0, hH0eq⟩ := cauchyEnd (f := g) hρ0 (by linarith) hU hUc hball hsegU
    (hgW.mono hUW)
  have hφ := phiD_continuousOn κ hb
  have htail : AnalyticOnNhd ℂ
      (fun ε : ℂ => ∫ w in c..(2 * (1 - b)), phiD κ b w / (ε + w)) (ball 0 (c / 2)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using piece_analytic (t₀ := 0) (η := c)
      (show c ≤ 2 * (1 - b) by linarith)
      (hφ.mono (Icc_subset_Icc hc0.le le_rfl)) (fun w hw => by
        rw [sub_zero, abs_of_nonneg (hc0.le.trans hw.1)]; exact hw.1)
  let r : ℝ := min ρ (1 / 2)
  have hr : 0 < r := lt_min hρ0 (by norm_num)
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrh : r ≤ 1 / 2 := min_le_right _ _
  have hε : ∀ s ∈ ball (2 : ℂ) r, (s - 2) / v ∈ ball (0 : ℂ) ρ := by
    intro s hs
    rw [mem_ball_zero_iff]
    exact (hdiv _).trans_lt ((mem_ball_iff_norm.mp hs).trans_le hrρ)
  let H : ℂ → ℂ := fun s => v * (H0 ((s - 2) / v) +
    ∫ w in c..(2 * (1 - b)), phiD κ b w / ((s - 2) / v + w))
  refine ⟨r, hr, H, ?_, ?_⟩
  · intro s hs
    have hεs := hε s hs
    have hεt := ball_subset_ball hρc hεs
    have haff : AnalyticAt ℂ (fun z : ℂ => (z - 2) / v) s := by
      exact ((analyticAt_id.sub analyticAt_const).div_const)
    have hh : AnalyticAt ℂ (fun s => H0 ((s - 2) / v) +
        ∫ w in c..(2 * (1 - b)), phiD κ b w / ((s - 2) / v + w)) s :=
      ((hH0 _ hεs).comp (f := fun z : ℂ => (z - 2) / v) haff).add
        ((htail _ hεt).comp (f := fun z : ℂ => (z - 2) / v) haff)
    exact analyticAt_const.mul hh
  · intro s hs hslog
    set ε : ℂ := (s - 2) / v with hεdef
    have hεs := hε s hs
    have hs0 : 0 < s.re := by
      have hnorm : ‖s - 2‖ < r := mem_ball_iff_norm.mp hs
      have hre : |s.re - 2| ≤ ‖s - 2‖ := by simpa using abs_re_le_norm (s - 2)
      have := (abs_lt.mp (hre.trans_lt hnorm)).1
      linarith
    have hΓ := Gamma_ne_zero_of_re_pos hs0
    have hsdiag : s ∉ segSS κ b := by
      rintro ⟨w, hw, he⟩
      have he' : ε = -(w : ℂ) := by dsimp [ε]; rw [he]; field_simp; ring
      have := hslog
      change ε ∈ slitPlane at this
      rw [he', neg_ofReal_mem_slitPlane] at this
      linarith [hw.1]
    have hden : ∀ w ∈ Icc (0 : ℝ) (2 * (1 - b)), ε + (w : ℂ) ≠ 0 :=
      fun w hw => slitPlane_ne_zero (slit_add_nonneg hslog hw.1)
    have hi : IntervalIntegrable (fun w : ℝ => phiD κ b w / (ε + w)) volume 0 (2 * (1-b)) :=
      (hφ.div (by fun_prop) hden).intervalIntegrable_of_Icc (by linarith [hb.2])
    have hi1 : IntervalIntegrable (fun w : ℝ => phiD κ b w / (ε + w)) volume 0 c :=
      (hφ.mono (Icc_subset_Icc le_rfl (show c ≤ 2 * (1-b) by linarith)) |>.div (by fun_prop)
        (fun w hw => hden w ⟨hw.1, hw.2.trans (by linarith)⟩)).intervalIntegrable_of_Icc hc0.le
    have hi2 : IntervalIntegrable (fun w : ℝ => phiD κ b w / (ε + w)) volume c (2 * (1-b)) :=
      (hφ.mono (Icc_subset_Icc hc0.le le_rfl) |>.div (by fun_prop)
        (fun w hw => hden w ⟨hc0.le.trans hw.1, hw.2⟩)).intervalIntegrable_of_Icc (by linarith)
    have hsmall : (∫ w in (0 : ℝ)..c, phiD κ b w / (ε + w)) =
        -g (-ε) * Complex.log ε + H0 ε := by
      rw [← hH0eq ε hεs hslog]
      apply intervalIntegral.integral_congr
      intro w hw
      rw [uIcc_of_le hc0.le] at hw
      dsimp only
      rw [phiD_eq_left κ ⟨hw.1, hw.2.trans hcb.le⟩]
    have hcoef : -v * g (-ε) = Gamma s * J 1 1 s := by
      have hsε : ε * v = s - 2 := div_mul_cancel₀ _ hv0
      have hJ : Gamma s * J 1 1 s = (s - 2) *
          ∫ τ in (0 : ℝ)..1, Gamma (1 + (τ : ℂ) * (s - 2)) *
            Gamma (s - (1 + (τ : ℂ) * (s - 2))) := by
        unfold J segInt Kern
        rw [intervalIntegral.integral_div]
        have he : s - 1 - 1 = s - 2 := by ring
        rw [he]
        field_simp
      rw [hJ]
      dsimp [g, kG, segInt]
      have hi' : (∫ τ in (0 : ℝ)..1, Gamma (1 - ((τ : ℂ) * -ε) * v) *
          Gamma (1 - (-ε - (τ : ℂ) * -ε) * v)) =
          ∫ τ in (0 : ℝ)..1, Gamma (1 + (τ : ℂ) * (s - 2)) *
            Gamma (s - (1 + (τ : ℂ) * (s - 2))) := by
        apply intervalIntegral.integral_congr
        intro τ _
        have he1 : 1 - ((τ : ℂ) * -ε) * v = 1 + (τ : ℂ) * (s - 2) := by
          linear_combination (τ : ℂ) * hsε
        have he2 : 1 - (-ε - (τ : ℂ) * -ε) * v = s - (1 + (τ : ℂ) * (s - 2)) := by
          linear_combination (1 - (τ : ℂ)) * hsε
        dsimp only
        rw [he1, he2]
      simp only [sub_zero, zero_add]
      rw [hi']
      linear_combination (hsε * (∫ τ in (0 : ℝ)..1, Gamma (1 + (τ : ℂ) * (s - 2)) *
        Gamma (s - (1 + (τ : ℂ) * (s - 2)))))
    rw [Dc_eq_diag κ hb hsdiag, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hsmall]
    dsimp [H, logAt]
    change v * (-g (-ε) * Complex.log ε + H0 ε + _) =
      Gamma s * J 1 1 s * Complex.log ε + v * (H0 ε + _)
    linear_combination hcoef * Complex.log ε

end GoldbachBoundaries.ThmA
