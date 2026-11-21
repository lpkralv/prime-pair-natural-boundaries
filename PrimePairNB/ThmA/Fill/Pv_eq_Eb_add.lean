import PrimePairNB.ThmA.G15_Kernel

/-!
# `Pv_eq_Eb_add`

`P_v = E_b + ∫_𝒮 dx/(z-x)` off the ray `1 - [0,∞)v`. Pure calculus, no RH.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

theorem lines_slantDir_ne_zero (κ : ℝ) : slantDir κ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [slantDir] at this

theorem lines_add_ofReal_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) {u : ℝ} (hu : 0 ≤ u) :
    w + (u : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left; simp; linarith
  · right; simpa using h

/-- `∫_0^a du/(w+u) = log(w+a) - log w` for `w ∈ slitPlane`, `a ≥ 0`. -/
theorem lines_integral_inv_add {w : ℂ} (hw : w ∈ slitPlane) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in (0 : ℝ)..a, 1 / (w + (u : ℂ)) = Complex.log (w + a) - Complex.log w := by
  have hmem : ∀ u ∈ [[(0 : ℝ), a]], w + (u : ℂ) ∈ slitPlane := fun u hu => by
    rw [uIcc_of_le ha] at hu
    exact lines_add_ofReal_mem_slitPlane hw hu.1
  have hderiv : ∀ u ∈ [[(0 : ℝ), a]],
      HasDerivAt (fun u : ℝ => Complex.log (w + (u : ℂ))) (1 / (w + (u : ℂ))) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => w + (u : ℂ)) 1 u := by
      simpa using (hasDerivAt_id u).ofReal_comp.const_add w
    exact h1.clog_real (hmem u hu)
  have hcont : ContinuousOn (fun u : ℝ => 1 / (w + (u : ℂ))) [[(0 : ℝ), a]] := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => slitPlane_ne_zero (hmem u hu)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp

/-- The closed form of `CauchyS`: `∫_𝒮 dx/(z-x) = Log((z - w_b)/v) - Log((z-1)/v)` when
`(z-1)/v ∈ slitPlane`. -/
theorem lines_CauchyS_eq {κ b : ℝ} (hb : b < 1) {z : ℂ} (hz : (z - 1) / slantDir κ ∈ slitPlane) :
    CauchyS κ b z =
      Complex.log ((z - wb κ b) / slantDir κ) - Complex.log ((z - 1) / slantDir κ) := by
  unfold CauchyS
  have hv := lines_slantDir_ne_zero κ
  set v := slantDir κ with hvdef
  set w := (z - 1) / v with hwdef
  have hkey : ∀ u : ℝ, v * (1 / (z - 1 + (u : ℂ) * v)) = 1 / (w + (u : ℂ)) := by
    intro u
    have : z - 1 + (u : ℂ) * v = v * (w + u) := by
      rw [hwdef]; field_simp
    rw [this]
    rcases eq_or_ne (w + (u : ℂ)) 0 with h0 | h0
    · simp [h0]
    · field_simp
  have hzwb : (z - wb κ b) / v = w + ((1 - b : ℝ) : ℂ) := by
    rw [hwdef, wb]; field_simp; ring
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hkey]
  rw [lines_integral_inv_add hz (by linarith : (0 : ℝ) ≤ 1 - b), hzwb]

end GroupE

/-- **`P_v = E_b + ∫_𝒮 dx/(z-x)`** off the ray `1 - [0,∞)v`. Pure calculus, no RH.

Sketch. `Eaux` cancels; it remains `Log((z-w_b)/v) - Log((z-1)/v) = ∫_0^{1-b} du/((z-1)/v + u)`,
which is `intervalIntegral.integral_eq_sub_of_hasDerivAt` for `u ↦ Log((z-1)/v + u)`, valid as
`(z-1)/v + u ∈ slitPlane` for `u ≥ 0` when `(z-1)/v ∈ slitPlane`; and
`(z-1)/v + (1-b) = (z - w_b)/v`, `v/(z - 1 + uv) = 1/((z-1)/v + u)`. -/
theorem Pv_eq_Eb_add {κ b : ℝ} (hb : b < 1) {z : ℂ}
    (hz : (z - 1) / slantDir κ ∈ slitPlane) :
    Pv κ z = Eb κ b z + CauchyS κ b z := by
  rw [GroupE.lines_CauchyS_eq hb hz, Pv, Eb, logAt]
  ring

end GoldbachBoundaries.ThmA
