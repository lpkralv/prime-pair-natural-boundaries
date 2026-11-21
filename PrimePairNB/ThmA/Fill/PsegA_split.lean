import PrimePairNB.ThmA.G15_Kernel

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

/-- **`P` along `s - 𝒮` near a pole of `Q`**: integrating the pole part of `Q` explicitly
(the paper's `P^{[s]}(s-x) = λ_a ℓ_s(x) + E_a(s-x) + c₀`, the local model; and the access lemma(i)).
Pure calculus, no RH.

Sketch. On the segment, `z(u') - a = v·w(u')` with `w(u') = (z(u') - a)/v`, `w' = 1`, and
`w(u') ∈ slitPlane`, so `u' ↦ c·Log(w(u'))` has derivative `c/w(u') = v·c/(z(u') - a)`
(`HasDerivAt.clog`). Split `Qcont = c/(z-a) + q` under the integral (`hQ`, `hseg`) and apply
`intervalIntegral.integral_eq_sub_of_hasDerivAt` to the first part. Integrability of `q ∘ z` from
`hq`. -/
theorem PsegA_split {κ b : ℝ} {A q : ℂ → ℂ} {c a s : ℂ} {u : ℝ} (hu : u ≤ 1 - b)
    (hQ : ∀ z ∈ halfPlane 0, z ∉ PoleSetQ → Qcont z = c / (z - a) + q z)
    (hseg : ∀ u' ∈ Icc u (1 - b), s - 1 + (u' : ℂ) * slantDir κ ∈ halfPlane 0 ∧
      s - 1 + (u' : ℂ) * slantDir κ ∉ PoleSetQ)
    (hq : ContinuousOn q ((fun u' : ℝ => s - 1 + (u' : ℂ) * slantDir κ) '' Icc u (1 - b)))
    (hlog : ∀ u' ∈ Icc u (1 - b), (s - 1 + (u' : ℂ) * slantDir κ - a) / slantDir κ ∈ slitPlane) :
    PsegA κ b A s u = A (s - wb κ b) +
      c * (Complex.log ((s - 1 + ((1 - b : ℝ) : ℂ) * slantDir κ - a) / slantDir κ) -
        Complex.log ((s - 1 + (u : ℂ) * slantDir κ - a) / slantDir κ)) +
      slantDir κ * ∫ u' in u..(1 - b), q (s - 1 + (u' : ℂ) * slantDir κ) := by
  have hv := slantDir_ne_zero κ
  have hne : ∀ t ∈ Icc u (1 - b), s - 1 + (t : ℂ) * slantDir κ - a ≠ 0 := by
    intro t ht he
    have := hlog t ht
    simp [he, Complex.slitPlane] at this
  have hp : IntervalIntegrable (fun t : ℝ => c / (s - 1 + (t : ℂ) * slantDir κ - a))
      volume u (1 - b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hu]
    exact continuousOn_const.div (by fun_prop) hne
  have hqi : IntervalIntegrable (fun t : ℝ => q (s - 1 + (t : ℂ) * slantDir κ))
      volume u (1 - b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hu]
    exact hq.comp (by fun_prop) (mapsTo_image _ _)
  have hd : ∀ t ∈ [[u, 1 - b]], HasDerivAt
      (fun t : ℝ => c * Complex.log ((s - 1 + (t : ℂ) * slantDir κ - a) / slantDir κ))
      (slantDir κ * (c / (s - 1 + (t : ℂ) * slantDir κ - a))) t := by
    intro t ht
    rw [uIcc_of_le hu] at ht
    have hinner := (((hasDerivAt_id (t : ℂ)).mul_const (slantDir κ)).const_add (s - 1)
      |>.sub_const a |>.div_const (slantDir κ)).comp_ofReal
    have h := (hinner.clog_real (hlog t ht)).const_mul c
    convert h using 1 <;> dsimp
    field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hp.const_mul (slantDir κ))
  rw [intervalIntegral.integral_const_mul] at hFTC
  have heq : (∫ t in u..(1 - b), Qcont (s - 1 + (t : ℂ) * slantDir κ)) =
      (∫ t in u..(1 - b), c / (s - 1 + (t : ℂ) * slantDir κ - a)) +
      ∫ t in u..(1 - b), q (s - 1 + (t : ℂ) * slantDir κ) := by
    rw [← intervalIntegral.integral_add hp hqi]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu] at ht
    exact hQ _ (hseg t ht).1 (hseg t ht).2
  rw [PsegA, heq, mul_add, hFTC]
  ring

end GoldbachBoundaries.ThmA
