import PrimePairNB.HInf.Fill.local_form_germFam
import PrimePairNB.HInf.Fill.Xc_analyticOn

/-!
# `not_analytic_of_germFam` (the contradiction behind the boundary theorem, in `v`)

`local_form_germFam` writes a member of `𝔊` near `x` as `Log_θ(v - x) X_x + h`; `ThmA.no_analytic_across_log` says this cannot
be analytic across the cut when `X_x'(x) ≠ 0`. A disc in `Re v > 1` meets the ray and the RH development's `cut` in the same set.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- Inside a disc in `Re v > 1`, the slit of `rayW` is the RH development's slit. -/
lemma slitDisc_eq {κ : ℝ} {x : ℂ} {r : ℝ} (hr : r ≤ x.re - 1) :
    slitDisc (slantDir κ) x r = ball x r \ rayW κ x := by
  ext s
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    rintro ⟨t, ht, rfl⟩
    refine hc ⟨t, ht, ?_, rfl⟩
    have h1 : 1 < (x - (t : ℂ) * slantDir κ).re := ThmA.ball_subset_HH hr hs
    simp [slantDir] at h1
    linarith
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    rintro ⟨t, ht, -, rfl⟩
    exact hc ⟨t, ht, rfl⟩

/-- A disc inside `Re v > 1` has radius at most `Re x - 1`. -/
lemma radius_le_of_ball_subset {top : EReal} {x : ℂ} {r : ℝ} (hr : 0 < r) (hsub : ball x r ⊆ VInf top) :
    r ≤ x.re - 1 := by
  by_contra hcon
  have hlt : x.re - 1 < r := not_le.mp hcon
  have hx : 1 < x.re := (hsub (mem_ball_self hr)).1.1
  have hmem : x - ((x.re - 1 : ℝ) : ℂ) ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact hlt
  have h1 : 1 < (x - ((x.re - 1 : ℝ) : ℂ)).re := (hsub hmem).1.1
  simp at h1

/-- **The contradiction behind the boundary theorem, in `v`.** `X_x'(x) ≠ 0`, `F` analytic on the punctured disc, and the germ of `F` at one
point of the slit disc lies in `𝔊`: impossible. -/
theorem not_analytic_of_germFam (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top)
    (hX : deriv (Xc k x) x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball x r \ rayW κ x ⊆ Om κ top ∧ ∀ r' : ℝ, 0 < r' → r' ≤ r → ∀ F : ℂ → ℂ,
      (∀ s ∈ ball x r', s ≠ x → AnalyticAt ℂ F s) → ∀ q ∈ ball x r' \ rayW κ x, ∀ C : ℂ,
        ¬ GermFam k top C q F := by
  obtain ⟨r, hr, hsub, hslit, hform⟩ := local_form_germFam hZ1 hZ2 hZ3 hK hκ hx hxV
  refine ⟨r, hr, hslit, fun r' hr' hr'r F hF q hq C hq' => ?_⟩
  have hr'x : r' ≤ x.re - 1 := hr'r.trans (radius_le_of_ball_subset hr hsub)
  obtain ⟨h, hh, hev⟩ := hform q ⟨ball_subset_ball hr'r hq.1, hq.2⟩ C F hq'
  have hXa : AnalyticOnNhd ℂ (Xc k x) (ball x r') := fun z hz =>
    Xc_analyticOn hZ1 hK hx z (hsub (ball_subset_ball hr'r hz)).1
  refine ThmA.no_analytic_across_log (κ := κ) hr' hr'x (X₀ := Xc k x)
    (H := fun v => Complex.log (slantDir κ) * Xc k x v + h v) (F := F) hXa hX
    (fun z hz => (analyticAt_const.mul (hXa z hz)).add (hh z (ball_subset_ball hr'r hz))) hF (s₁ := q)
    (by rw [slitDisc_eq hr'x]; exact hq) ?_
  filter_upwards [hev] with v hv
  rw [hv]
  simp only [logK, logAt]
  ring

end GoldbachBoundaries.HInf.Fill
