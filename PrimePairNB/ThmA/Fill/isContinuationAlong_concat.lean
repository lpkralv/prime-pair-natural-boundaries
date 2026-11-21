import PrimePairNB.ThmA.G13_Continuation

/-!
# `isContinuationAlong_concat`

Proof: reparametrise `f₁` by `t ↦ projIcc (2t)` and `f₂` by `t ↦ projIcc (2t - 1)`
(`continuationAlong_comp`), glue at `t = 1/2`, and use `hlink` at the junction.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

namespace ConcatFill

/-- `t ↦ 2t`, clamped to `[0,1]`. -/
def m₁ : C(unitInterval, unitInterval) :=
  ⟨fun t => projIcc 0 1 zero_le_one (2 * (t : ℝ)), continuous_projIcc.comp (by fun_prop)⟩

/-- `t ↦ 2t - 1`, clamped to `[0,1]`. -/
def m₂ : C(unitInterval, unitInterval) :=
  ⟨fun t => projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1), continuous_projIcc.comp (by fun_prop)⟩

theorem concatPath_apply (γ₁ γ₂ : C(unitInterval, ℂ)) (h : γ₂ 0 = γ₁ 1) (t : unitInterval) :
    concatPath γ₁ γ₂ h t = if (t : ℝ) ≤ 1 / 2 then γ₁ (m₁ t) else γ₂ (m₂ t) := rfl

theorem m₁_half : m₁ ⟨1 / 2, by norm_num, by norm_num⟩ = 1 := by
  ext; simp [m₁]

theorem m₂_half : m₂ ⟨1 / 2, by norm_num, by norm_num⟩ = 0 := by
  ext; simp [m₂]

end ConcatFill

open ConcatFill in
/-- **Concatenation of continuations.** Continuations along `γ₁` and `γ₂` (`γ₂ 0 = γ₁ 1`)
whose germs match at the junction give a continuation along `concatPath γ₁ γ₂ h` (`Path.trans`)
with the same initial and terminal functions.

Sketch. `Path.trans` runs `γ₁ (2t)` on `[0, 1/2]` and `γ₂ (2t - 1)` on `[1/2, 1]`
(`Path.trans_apply`). Put `f t = f₁ (2t)` for `t ≤ 1/2`, `f₂ (2t-1)` for `t > 1/2` (with
`Set.projIcc` to stay in `[0,1]`). `analyticAt` is inherited. `locallyEq` at `t ≠ 1/2` is inherited
(reparametrisation by an affine map); at `t = 1/2`: from the left it is `f₁`'s `locallyEq` at `1`;
from the right, `f₂ (2t'-1) =ᶠ f₂ 0` near `γ₂ (2t'-1)` and `f₂ 0 =ᶠ f₁ 1` near every point close to
`γ₂ 0` (`hlink.eventuallyEq_nhds`). -/
theorem isContinuationAlong_concat {γ₁ γ₂ : C(unitInterval, ℂ)} (h : γ₂ 0 = γ₁ 1)
    {f₁ f₂ : unitInterval → ℂ → ℂ} (hf₁ : IsContinuationAlong γ₁ f₁)
    (hf₂ : IsContinuationAlong γ₂ f₂) (hlink : f₂ 0 =ᶠ[𝓝 (γ₂ 0)] f₁ 1) :
    ∃ f : unitInterval → ℂ → ℂ, IsContinuationAlong (concatPath γ₁ γ₂ h) f ∧
      f 0 = f₁ 0 ∧ f 1 = f₂ 1 := by
  classical
  set f : unitInterval → ℂ → ℂ := fun t => if (t : ℝ) ≤ 1 / 2 then f₁ (m₁ t) else f₂ (m₂ t)
    with hfdef
  have h₁ := continuationAlong_comp hf₁ m₁
  have h₂ := continuationAlong_comp hf₂ m₂
  have hle : ∀ t : unitInterval, (t : ℝ) ≤ 1 / 2 →
      f t = f₁ (m₁ t) ∧ concatPath γ₁ γ₂ h t = γ₁ (m₁ t) := fun t ht =>
    ⟨by simp only [hfdef]; exact ite_eq_left_iff.mpr (fun h => absurd ht h), by rw [concatPath_apply]; exact ite_eq_left_iff.mpr (fun h => absurd ht h)⟩
  have hgt : ∀ t : unitInterval, ¬ (t : ℝ) ≤ 1 / 2 →
      f t = f₂ (m₂ t) ∧ concatPath γ₁ γ₂ h t = γ₂ (m₂ t) := fun t ht =>
    ⟨by simp only [hfdef]; exact ite_eq_right_iff.mpr (fun h => absurd h ht), by rw [concatPath_apply]; exact ite_eq_right_iff.mpr (fun h => absurd h ht)⟩
  refine ⟨f, ⟨fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [(hle t ht).1, (hle t ht).2]; exact h₁.analyticAt t
    · rw [(hgt t ht).1, (hgt t ht).2]; exact h₂.analyticAt t
  · rcases lt_trichotomy (t : ℝ) (1 / 2) with ht | ht | ht
    · have hev : ∀ᶠ t' : unitInterval in 𝓝 t, (t' : ℝ) ≤ 1 / 2 :=
        (continuous_subtype_val.tendsto t).eventually (eventually_le_nhds ht)
      filter_upwards [hev, h₁.locallyEq t] with t' ht' h1
      rw [(hle t' ht').1, (hle t' ht').2, (hle t ht.le).1]
      exact h1
    · have htq : t = ⟨1 / 2, by norm_num, by norm_num⟩ := Subtype.ext ht
      subst htq
      have hft : f ⟨1 / 2, by norm_num, by norm_num⟩ = f₁ 1 := by
        rw [(hle _ le_rfl).1, m₁_half]
      -- junction: germs of `f₂ 0` and `f₁ 1` agree near `γ₂ (m₂ t')` for `t'` near `1/2`
      have hcont : Tendsto (fun t' => γ₂ (m₂ t')) (𝓝 ⟨1 / 2, by norm_num, by norm_num⟩)
          (𝓝 (γ₂ 0)) := by
        have := (γ₂.continuous.comp m₂.continuous).tendsto ⟨1 / 2, by norm_num, by norm_num⟩
        rw [Function.comp_apply, m₂_half] at this
        exact this
      have hj : ∀ᶠ t' in 𝓝 (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval),
          f₂ 0 =ᶠ[𝓝 (γ₂ (m₂ t'))] f₁ 1 := hcont.eventually hlink.eventuallyEq_nhds
      filter_upwards [h₁.locallyEq _, h₂.locallyEq _, hj] with t' h1 h2 hj'
      rw [hft]
      by_cases ht' : (t' : ℝ) ≤ 1 / 2
      · rw [(hle t' ht').1, (hle t' ht').2]
        rw [m₁_half] at h1
        exact h1
      · rw [(hgt t' ht').1, (hgt t' ht').2]
        have h2' : f₂ (m₂ t') =ᶠ[𝓝 (γ₂ (m₂ t'))] f₂ 0 := by rw [m₂_half] at h2; exact h2
        exact h2'.trans hj'
    · have hev : ∀ᶠ t' : unitInterval in 𝓝 t, ¬ (t' : ℝ) ≤ 1 / 2 :=
        (continuous_subtype_val.tendsto t).eventually
          ((eventually_gt_nhds ht).mono fun _ hx => not_le.mpr hx)
      filter_upwards [hev, h₂.locallyEq t] with t' ht' h2
      rw [(hgt t' ht').1, (hgt t' ht').2, (hgt t (not_le.mpr ht)).1]
      exact h2
  · have : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by simp
    rw [(hle 0 this).1]
    congr 1; ext; simp [m₁]
  · have : ¬ ((1 : unitInterval) : ℝ) ≤ 1 / 2 := by simp; norm_num
    rw [(hgt 1 this).1]
    congr 1; ext; simp [m₂]; norm_num

end GoldbachBoundaries.ThmA
