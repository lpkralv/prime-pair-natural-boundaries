import PrimePairNB.ThmA.G20_Branches
import PrimePairNB.ThmA.Fill.slitDisc_facts

/-!
# `no_analytic_across_log`

`F = X₀·Log_α + H` on the slit disc (identity theorem; the slit disc is open and connected,
`slitDisc_facts`, in `Fill/slitDisc_facts.lean`). `X₀(x) ≠ 0` at some `x = α - t v`, `t > 0` small (`HasDerivAt.eventually_ne`,
as `deriv X₀ α ≠ 0`). At `x`, `F` is continuous, but along `x + iηv`, `η → 0±`, the right side
tends to `X₀(x)·Log(-t) + H(x)` resp. `X₀(x)·(log t - iπ) + H(x)`, whose imaginary parts of the
logarithms are `π` and `-π`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- **No analytic continuation across a logarithmic cut with non-zero coefficient**
(the boundary theorem for `G` step 4, the every-path statement "monodromy `M_α ≢ 0`"; general).

Sketch. `X₀·Log_α + H` is analytic on the slit disc (`slitDisc_facts`: off the cut,
`(s-α)/v ∈ slitPlane`), which is connected, so `F = X₀ Log_α + H` on it (identity theorem from
`s₁`). `X₀` has an isolated zero at most at `α` (`deriv X₀ α ≠ 0`), so `X₀(x) ≠ 0` at some
`x = α - tv`, `0 < t` small, in the ball. At `x`, `F` is continuous, but approaching from
`Im((s-α)/v) > 0` and `< 0` the right side tends to `X₀(x)(log|·| ± iπ) + H(x)`
(`Complex.continuousWithinAt_log_of_re_neg_of_im_zero`,
`Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero`), which differ by `2πi X₀(x) ≠ 0`. -/
theorem no_analytic_across_log {κ : ℝ} {α : ℂ} {ε : ℝ} (hε : 0 < ε) (hεα : ε ≤ α.re - 1)
    {X₀ H F : ℂ → ℂ} (hX : AnalyticOnNhd ℂ X₀ (ball α ε)) (hX' : deriv X₀ α ≠ 0)
    (hH : AnalyticOnNhd ℂ H (ball α ε)) (hF : ∀ s ∈ ball α ε, s ≠ α → AnalyticAt ℂ F s)
    {s₁ : ℂ} (hs₁ : s₁ ∈ slitDisc (slantDir κ) α ε)
    (hEq : F =ᶠ[𝓝 s₁] fun s => X₀ s * logAt (slantDir κ) α s + H s) : False := by
  set v := slantDir κ with hvdef
  have hv : v ≠ 0 := slantDir_ne_zero κ
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨hopen, hconn, hcutiff⟩ := slitDisc_facts κ hε hεα
  set G : ℂ → ℂ := fun s => X₀ s * logAt v α s + H s with hGdef
  -- `α` lies on the cut, so points of the slit disc are `≠ α`
  have hαcut : α ∈ cut v α := ⟨0, le_rfl, by linarith, by simp⟩
  have hGan : AnalyticOnNhd ℂ G (slitDisc v α ε) := by
    intro s hs
    have hslit : (s - α) / v ∈ slitPlane := (hcutiff s hs.1).mp hs.2
    have hlog : AnalyticAt ℂ (fun s => logAt v α s) s := by
      simp only [logAt]
      exact AnalyticAt.clog (by fun_prop) hslit
    exact ((hX s hs.1).mul hlog).add (hH s hs.1)
  have hFan : AnalyticOnNhd ℂ F (slitDisc v α ε) := fun s hs =>
    hF s hs.1 (fun h => hs.2 (h ▸ hαcut))
  have hFG : EqOn F G (slitDisc v α ε) :=
    hFan.eqOn_of_preconnected_of_eventuallyEq hGan hconn hs₁ hEq
  -- a point `x = α - t v` of the cut with `X₀ x ≠ 0`
  have hgd : HasDerivAt (fun t : ℝ => X₀ (α - (t : ℂ) * v)) (deriv X₀ α * (-v)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => α - (t : ℂ) * v) (-v) 0 := by
      have := ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const v).const_sub α
      simpa using this.comp_ofReal
    have h2 : HasDerivAt X₀ (deriv X₀ α) (α - ((0 : ℝ) : ℂ) * v) := by
      simpa using ((hX α (mem_ball_self hε)).differentiableAt).hasDerivAt
    exact h2.comp (0 : ℝ) h1
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), X₀ (α - ((t : ℝ) : ℂ) * v) ≠ 0 :=
    hgd.eventually_ne (mul_ne_zero hX' (neg_ne_zero.mpr hv))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), X₀ (α - ((t : ℝ) : ℂ) * v) ≠ 0 ∧ t * ‖v‖ < ε ∧ 0 < t := by
    have h1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), X₀ (α - ((t : ℝ) : ℂ) * v) ≠ 0 :=
      nhdsWithin_mono _ (fun t ht => ne_of_gt ht) hne
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t * ‖v‖ < ε := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun t : ℝ => t * ‖v‖) (𝓝 0) (𝓝 (0 * ‖v‖)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this (Iio_mem_nhds hε)
    filter_upwards [h1, h2, self_mem_nhdsWithin] with t ht1 ht2 ht3 using ⟨ht1, ht2, ht3⟩
  obtain ⟨t, hXt, htv, ht⟩ := hsmall.exists
  set x := α - (t : ℂ) * v with hxdef
  have hxball : x ∈ ball α ε := by
    rw [mem_ball, dist_eq, hxdef, sub_sub_cancel_left, norm_neg, norm_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htv
  have hxne : x ≠ α := by
    intro h
    have : (t : ℂ) * v = 0 := by rw [hxdef] at h; linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ht.ne' (by exact_mod_cast h')
    · exact hv h'
  have hFc : ContinuousAt F x := (hF x hxball hxne).continuousAt
  -- the transversal path `x + iηv`
  set p : ℝ → ℂ := fun η => x + (η : ℂ) * I * v with hpdef
  set q : ℝ → ℂ := fun η => -(t : ℂ) + (η : ℂ) * I with hqdef
  have hpq : ∀ η, (p η - α) / v = q η := by
    intro η
    rw [div_eq_iff hv]
    simp only [hpdef, hqdef, hxdef]
    ring
  have hpc : Continuous p := by simp only [hpdef]; fun_prop
  have hqc : Continuous q := by simp only [hqdef]; fun_prop
  have hp0 : p 0 = x := by simp [hpdef]
  have hq0 : q 0 = -(t : ℂ) := by simp [hqdef]
  have hqim : ∀ η, (q η).im = η := by intro η; simp [hqdef]
  -- near `η = 0`, `η ≠ 0`, the path lies in the slit disc
  have hpball : ∀ᶠ η in 𝓝 (0 : ℝ), p η ∈ ball α ε := by
    have := hpc.tendsto 0
    rw [hp0] at this
    exact this (isOpen_ball.mem_nhds hxball)
  have hpslit : ∀ᶠ η in 𝓝[≠] (0 : ℝ), p η ∈ slitDisc v α ε := by
    filter_upwards [nhdsWithin_le_nhds hpball, self_mem_nhdsWithin] with η hη hη0
    refine ⟨hη, (hcutiff _ hη).mpr ?_⟩
    rw [hpq, mem_slitPlane_iff]
    right
    rw [hqim]
    exact hη0
  have hlim : ∀ (L : ℂ) (l : Filter ℝ), l ≤ 𝓝[≠] (0 : ℝ) → l.NeBot →
      Tendsto (fun η => Complex.log (q η)) l (𝓝 L) → F x = X₀ x * L + H x := by
    intro L l hl _ hL
    have hpx : Tendsto p l (𝓝 x) := by
      have := (hpc.tendsto 0).mono_left (hl.trans nhdsWithin_le_nhds)
      rwa [hp0] at this
    have hF1 : Tendsto (fun η => F (p η)) l (𝓝 (F x)) := by
      exact hFc.tendsto.comp hpx
    have hX1 : Tendsto (fun η => X₀ (p η)) l (𝓝 (X₀ x)) := by
      exact (hX x hxball).continuousAt.tendsto.comp hpx
    have hH1 : Tendsto (fun η => H (p η)) l (𝓝 (H x)) := by
      exact (hH x hxball).continuousAt.tendsto.comp hpx
    have hG1 : Tendsto (fun η => G (p η)) l (𝓝 (X₀ x * L + H x)) := by
      have : (fun η => G (p η)) = fun η => X₀ (p η) * Complex.log (q η) + H (p η) := by
        funext η
        simp only [hGdef, logAt, hpq]
      rw [this]
      exact (hX1.mul hL).add hH1
    have hev : (fun η => F (p η)) =ᶠ[l] fun η => G (p η) := by
      filter_upwards [hl hpslit] with η hη using hFG hη
    exact tendsto_nhds_unique (hF1.congr' hev) hG1
  -- the two one-sided limits of `Log(q η)`
  have hre : (-(t : ℂ)).re < 0 := by simp [ht]
  have him : (-(t : ℂ)).im = 0 := by simp
  have hup : Tendsto (fun η => Complex.log (q η)) (𝓝[>] (0 : ℝ)) (𝓝 (Complex.log (-(t : ℂ)))) := by
    have h1 := (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto
    refine h1.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have := (hqc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hq0] at this
    · filter_upwards [self_mem_nhdsWithin] with η hη
      show 0 ≤ (q η).im
      rw [hqim]; exact le_of_lt hη
  have hdown : Tendsto (fun η => Complex.log (q η)) (𝓝[<] (0 : ℝ))
      (𝓝 (Real.log ‖-(t : ℂ)‖ - Real.pi * I)) := by
    have h1 := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    refine h1.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have := (hqc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
      rwa [hq0] at this
    · filter_upwards [self_mem_nhdsWithin] with η hη
      show (q η).im < 0
      rw [hqim]; exact hη
  have e1 := hlim _ (𝓝[>] (0 : ℝ))
    (nhdsWithin_mono _ (fun η (hη : η ∈ Ioi (0 : ℝ)) => ne_of_gt hη)) inferInstance hup
  have e2 := hlim _ (𝓝[<] (0 : ℝ))
    (nhdsWithin_mono _ (fun η (hη : η ∈ Iio (0 : ℝ)) => ne_of_lt hη)) inferInstance hdown
  have hdiff : X₀ x * (Complex.log (-(t : ℂ)) - (Real.log ‖-(t : ℂ)‖ - Real.pi * I)) = 0 := by
    linear_combination e2 - e1
  have hL : Complex.log (-(t : ℂ)) - (Real.log ‖-(t : ℂ)‖ - Real.pi * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have harg : arg (-(t : ℂ)) = Real.pi := by
      have := arg_ofReal_of_neg (x := -t) (by linarith)
      simpa using this
    simp [log_im, harg] at this
  exact mul_ne_zero hXt hL hdiff

end GoldbachBoundaries.ThmA
