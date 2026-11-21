import PrimePairNB.HInf.Fill.every_path_S
import PrimePairNB.HInf.Fill.exists_admS
import PrimePairNB.HInf.Fill.Dth_eq
import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.isPinchKernel_S

/-!
# HInf: admissible germs of `S` exist at every point of `{σ > 0} ∖ catS`

`boundary_S` says that no admissible germ `AdmS g s₁` with `s₁` in a disc about a point of `Re s = 0` extends
meromorphically over the disc. This file shows that such germs exist, so the statement is not vacuous: under `(H_∞)`,
(Z1) to (Z3), a point carries an admissible germ of `S` exactly when it lies in `{σ > 0} ∖ catS`
(`exists_admS_iff`), and every disc about a point of `Re s = 0` contains such a point (`exists_admS_near`).

The proof uses the fixed sheet `D^θ` in the variable `v = 2s + 1`. Fix a point `v₁` off `Σ + Σ`; for all but countably many
slopes `κ` it lies on no westward cut `rayW κ x`, `x ∈ Σ + Σ` (`exists_slope_not_mem_cuts`). The eastward ray from `v₁` in
direction `κ` then meets no cut either (a cut through a point of the ray would contain `v₁`), so its part in `Re v ≤ 2`
lies in `Ω_κ`, where `D^κ` is holomorphic (`Fill.Dth_analyticOn`). On `2 < Re v < 3`, `D^κ = S((v-1)/2)`
(`Fill.Dth_eq`). So the function equal to `D^κ(2s + 1)` on `Re(2s + 1) < 5/2` and to `S` elsewhere is `S` on all of
`σ > 1/2` and analytic at every point of the ray; it is its own continuation along the ray, from a start in `σ > 1` back
to `s₁`, and its germ at `s₁` is admissible.

Without `(H_∞)` the same argument gives the points with `2B_∞ < Re(2s + 1)` (`exists_admS_of_two_Binf_lt`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- Moving east along a `κ`-line from a point that lies on no `κ`-cut keeps it off every `κ`-cut: a cut through the new
point would also contain the old one. -/
theorem add_not_mem_cuts {κ : ℝ} {v : ℂ} (hv : v ∉ ⋃ x ∈ Pinch, rayW κ x) {t : ℝ} (ht : 0 ≤ t) :
    v + (t : ℂ) * slantDir κ ∉ ⋃ x ∈ Pinch, rayW κ x := by
  simp only [mem_iUnion, not_exists] at hv ⊢
  rintro x hx ⟨u, hu, he⟩
  refine hv x hx ⟨u + t, by linarith, ?_⟩
  push_cast
  linear_combination he

/-- A point off `Σ + Σ` lies on no `κ`-cut, for some slope `κ` (indeed for all but countably many). -/
theorem exists_slope_not_mem_cuts {v : ℂ} (hv : v ∉ Pinch) : ∃ κ : ℝ, v ∉ ⋃ x ∈ Pinch, rayW κ x := by
  have hB := Fill.pinch_countable.image (fun x : ℂ => (x - v).im / (x - v).re)
  by_contra hall
  push Not at hall
  refine Cardinal.not_countable_real (hB.mono fun κ _ => ?_)
  have hκ := hall κ
  simp only [mem_iUnion] at hκ
  obtain ⟨x, hx, t, -, hvx⟩ := hκ
  have hne : x ≠ v := fun h => hv (h ▸ hx)
  exact ⟨x, hx, Fill.slope_eq hne (by rw [hvx]; ring)⟩

/-- The function used below: `D^κ(2s + 1)` on `Re(2s + 1) < 5/2`, `S` elsewhere. -/
def sheetS (κ : ℝ) (s : ℂ) : ℂ := if (2 * s + 1).re < 5 / 2 then Dth kS κ (2 * s + 1) else Sser s

lemma re_two_mul_add_one (s : ℂ) : (2 * s + 1).re = 2 * s.re + 1 := by
  simp

/-- `sheetS κ` is `S` near every point of `σ > 1/2`. -/
lemma sheetS_eventuallyEq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (κ : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    sheetS κ =ᶠ[𝓝 s] Sser := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  have hw' : (1 / 2 : ℝ) < w.re := hw
  unfold sheetS
  split_ifs with hlt
  · rw [Fill.Dth_eq hZ1 hZ2 hZ3 Fill.isPinchKernel_S κ (by rw [re_two_mul_add_one]; linarith)
      (by linarith)]
    simp only [DS]
    congr 1
    ring
  · rfl

/-- `sheetS κ` is analytic at a point whose image `2s + 1` lies in `Ω_κ` with `Re(2s + 1) < 5/2`. -/
lemma sheetS_analyticAt_of_mem_Om (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {κ : ℝ} {s : ℂ} (hOm : 2 * s + 1 ∈ Om κ 3)
    (hlt : (2 * s + 1).re < 5 / 2) : AnalyticAt ℂ (sheetS κ) s := by
  have hD : AnalyticAt ℂ (fun w : ℂ => Dth kS κ (2 * w + 1)) s := by
    have haff : AnalyticAt ℂ (fun w : ℂ => 2 * w + 1) s :=
      (analyticAt_const.mul analyticAt_id).add analyticAt_const
    exact (Fill.Dth_analyticOn hZ1 hZ2 hZ3 Fill.isPinchKernel_S κ _ hOm).comp (f := fun w : ℂ => 2 * w + 1) haff
  refine hD.congr ?_
  have hopen : IsOpen {w : ℂ | (2 * w + 1).re < 5 / 2} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hlt] with w hw
  unfold sheetS
  split_ifs with h
  · rfl
  · exact absurd hw h

/-- **The construction.** If `v₁ = 2s₁ + 1` has `2B_∞ < Re v₁`, `0 < Re s₁`, and lies on no `κ`-cut, then the germ of
`sheetS κ` at `s₁` is an admissible germ of `S`. The path is the `κ`-segment from `s₁ + slantDir κ` (in `σ > 1`) to `s₁`. -/
theorem admS_sheetS (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {κ : ℝ} {s₁ : ℂ} (h0 : 0 < s₁.re)
    (hB : 2 * Binf < (2 * s₁ + 1).re) (hv : 2 * s₁ + 1 ∉ ⋃ x ∈ Pinch, rayW κ x) : AdmS (sheetS κ) s₁ := by
  let γ : C(unitInterval, ℂ) :=
    ⟨fun t => s₁ + (((1 : ℝ) - (t : ℝ) : ℝ) : ℂ) * slantDir κ, by fun_prop⟩
  have hγ : ∀ t : unitInterval, γ t = s₁ + (((1 : ℝ) - (t : ℝ) : ℝ) : ℂ) * slantDir κ := fun _ => rfl
  have hre : ∀ t : unitInterval, (γ t).re = s₁.re + (1 - (t : ℝ)) := by
    intro t
    rw [hγ]
    simp [slantDir]
  have hv2 : ∀ t : unitInterval,
      2 * γ t + 1 = (2 * s₁ + 1) + ((2 * (1 - (t : ℝ)) : ℝ) : ℂ) * slantDir κ := by
    intro t
    rw [hγ]
    push_cast
    ring
  have hcut : ∀ t : unitInterval, 2 * γ t + 1 ∉ ⋃ x ∈ Pinch, rayW κ x := by
    intro t
    rw [hv2]
    exact add_not_mem_cuts hv (by nlinarith [t.2.2])
  have hle : ∀ t : unitInterval, s₁.re ≤ (γ t).re := by
    intro t
    rw [hre]
    linarith [t.2.2]
  refine ⟨γ, fun t => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · show 0 < (γ t).re
    linarith [hle t]
  · intro hc
    have hP := (Fill.mem_catS_iff.mp hc).2
    apply hcut t
    simp only [mem_iUnion]
    exact ⟨_, hP, 0, le_refl _, by simp⟩
  · show 1 < (γ 0).re
    rw [hre]
    simp
    linarith
  · rw [hγ]
    simp
  · refine ThmA.isTerminalGerm_of_analyticAt (fun t => ?_) ?_
    · by_cases ht : 1 / 2 < (γ t).re
      · exact (Fill.Sser_analyticAt ht).congr (sheetS_eventuallyEq hZ1 hZ2 hZ3 κ ht).symm
      · push Not at ht
        have hr : (2 * γ t + 1).re ≤ 2 := by rw [re_two_mul_add_one]; linarith
        have hr₁ : (2 * s₁ + 1).re ≤ (2 * γ t + 1).re := by
          rw [re_two_mul_add_one, re_two_mul_add_one]; linarith [hle t]
        have hr₀ : 1 < (2 * s₁ + 1).re := by rw [re_two_mul_add_one]; linarith
        refine sheetS_analyticAt_of_mem_Om hZ1 hZ2 hZ3 ⟨⟨⟨by linarith, ?_⟩, by linarith⟩, hcut t⟩
          (by linarith)
        have : ((2 * γ t + 1).re : EReal) < ((3 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
        exact this.trans_eq (by norm_cast)
    · have h1 : 1 / 2 < (γ 0).re := by rw [hre]; simp; linarith
      exact sheetS_eventuallyEq hZ1 hZ2 hZ3 κ h1

/-- **Admissible germs of `S` exist off the catalogue, without `(H_∞)`.** Every `s₁` with `0 < Re s₁`,
`2B_∞ < Re(2s₁ + 1)` and `s₁ ∉ catS` carries an admissible germ of `S`. -/
theorem exists_admS_of_two_Binf_lt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {s₁ : ℂ} (h0 : 0 < s₁.re)
    (hB : 2 * Binf < (2 * s₁ + 1).re) (hc : s₁ ∉ catS) : ∃ g : ℂ → ℂ, AdmS g s₁ := by
  have hP : 2 * s₁ + 1 ∉ Pinch := fun hP => hc (Fill.mem_catS_iff.mpr ⟨h0, hP⟩)
  obtain ⟨κ, hκ⟩ := exists_slope_not_mem_cuts hP
  exact ⟨sheetS κ, admS_sheetS hZ1 hZ2 hZ3 h0 hB hκ⟩

/-- **Where admissible germs of `S` exist (paper: Lemma sep and Theorem branches(b)).** Under `(H_∞)`, (Z1) to (Z3), a
point carries an admissible germ of `S` if and only if it lies in `{σ > 0} ∖ catS`. -/
theorem exists_admS_iff (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {s₁ : ℂ} :
    (∃ g : ℂ → ℂ, AdmS g s₁) ↔ s₁ ∈ halfPlane 0 \ catS := by
  constructor
  · rintro ⟨g, hg⟩
    exact Fill.admS_mem hg
  · rintro ⟨h0, hc⟩
    have h0' : 0 < s₁.re := h0
    refine exists_admS_of_two_Binf_lt hZ1 hZ2 hZ3 h0' ?_ hc
    rw [M2.Binf_eq_half_of_Hinf hZ1 hH, re_two_mul_add_one]
    linarith

/-- **`boundary_S` is not vacuous.** Under `(H_∞)`, (Z1) to (Z3), every disc about a point of `Re s = 0` contains a point
carrying an admissible germ of `S`. -/
theorem exists_admS_near (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ y : ℝ, ∀ r : ℝ, 0 < r → ∃ (s₁ : ℂ) (g : ℂ → ℂ), s₁ ∈ ball ((y : ℂ) * I) r ∧ AdmS g s₁ := by
  intro y r hr
  have hV : IsOpen (ball ((y : ℂ) * I) r ∩ halfPlane 0) :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hne : (ball ((y : ℂ) * I) r ∩ halfPlane 0).Nonempty := by
    refine ⟨((r / 2 : ℝ) : ℂ) + (y : ℂ) * I, ?_, ?_⟩
    · rw [mem_ball, dist_eq, add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · show (0 : ℝ) < (((r / 2 : ℝ) : ℂ) + (y : ℂ) * I).re
      simp
      linarith
  obtain ⟨w, ⟨hwb, hw0⟩, hwc⟩ := Fill.exists_not_catS hV hne
  obtain ⟨g, hg⟩ := (exists_admS_iff hH hZ1 hZ2 hZ3).mpr ⟨hw0, hwc⟩
  exact ⟨w, g, hwb, hg⟩

end GoldbachBoundaries.HInf
