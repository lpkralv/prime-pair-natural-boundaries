import PrimePairNB.ThmA.G20_Branches
import PrimePairNB.ThmA.Fill.GCommon
import PrimePairNB.ThmA.Fill.J_spec
import PrimePairNB.ThmA.Fill.cutDisc_facts

/-!
# `jump_of_access` (the jump corollary, one-sided form)

Proof. (1) Transfer: if two discs centred on the line of `cut_α` meet, both carry continuations of
`Gn` from their `+` parts, and the first satisfies the jump on its `-` part, so does the second
(identity theorem twice, on the convex overlap and on the convex `-` part). (2) Near `α` the jump
holds by the local form `Gn = X·Log_α + H` (the continuation of `Log` from `Im > 0` is
`Log(-w) + iπ`, which is `Log w + 2πi` on `Im < 0`). (3) "The jump holds for every cut disc at
`α - tv`" is locally constant in `t ∈ (0, Re α - 1)` (access discs plus (1)), so it holds
everywhere (`IsPreconnected.induction₂`).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- Step (1): transfer of the jump between two meeting discs centred on the line of `cut_α`. -/
theorem G_jump_transfer {κ : ℝ} {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn) {α : ℂ}
    (hα : α ∈ catalogue) {s₁ s₂ : ℂ} (h₁ : ((s₁ - α) / slantDir κ).im = 0)
    (hs₂ : s₂ ∈ cut (slantDir κ) α) {ρ₁ ρ₂ : ℝ} (hD₂ : IsCutDisc κ α s₂ ρ₂) {F₁ F₂ : ℂ → ℂ}
    (hF₁ : AnalyticOnNhd ℂ F₁ (ball s₁ ρ₁)) (hF₂ : AnalyticOnNhd ℂ F₂ (ball s₂ ρ₂))
    (hup₁ : EqOn F₁ Gn (upperPart κ α s₁ ρ₁)) (hup₂ : EqOn F₂ Gn (upperPart κ α s₂ ρ₂))
    (hjump₁ : EqOn F₁ (fun s => Gn s + Mon α s) (lowerPart κ α s₁ ρ₁))
    (hne : (ball s₁ ρ₁ ∩ ball s₂ ρ₂).Nonempty) :
    EqOn F₂ (fun s => Gn s + Mon α s) (lowerPart κ α s₂ ρ₂) := by
  have h₂ := G_im_cut hs₂
  obtain ⟨⟨zu, hzuO, hzu⟩, ⟨zl, hzlO, hzl⟩⟩ := G_inter_upper_lower h₁ h₂ hne
  set O := ball s₁ ρ₁ ∩ ball s₂ ρ₂ with hO
  have hOo : IsOpen O := isOpen_ball.inter isOpen_ball
  -- `F₁ = F₂` on the overlap.
  have hF12 : EqOn F₁ F₂ O := by
    refine G_eqOn_of_subset (hF₁.mono inter_subset_left) (hF₂.mono inter_subset_right)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
      (hOo.inter (isOpen_lt continuous_const (by fun_prop))) inter_subset_left
      (W := O ∩ {z | 0 < ((z - α) / slantDir κ).im}) ⟨hzuO, hzu⟩ ?_
    intro z hz
    rw [hup₁ ⟨hz.1.1, hz.2⟩, hup₂ ⟨hz.1.2, hz.2⟩]
  obtain ⟨-, -, hlowΩ, -, hlowo, -, hlowc⟩ := cutDisc_facts hs₂ hD₂
  have hGM : AnalyticOnNhd ℂ (fun s => Gn s + Mon α s) (lowerPart κ α s₂ ρ₂) := fun z hz =>
    (hP.analyticOn z (hlowΩ hz)).add (Mon_analyticOn hα z (Omega_subset (hlowΩ hz)).1)
  refine G_eqOn_of_subset (hF₂.mono fun z hz => hz.1) hGM hlowc.isPreconnected
    (hOo.inter (isOpen_lt (by fun_prop) continuous_const))
    (W := O ∩ {z | ((z - α) / slantDir κ).im < 0}) (fun z hz => ⟨hz.1.2, hz.2⟩) ⟨hzlO, hzl⟩ ?_
  intro z hz
  rw [← hF12 hz.1]
  exact hjump₁ ⟨hz.1.1, hz.2⟩

/-- "The jump holds for every cut disc centred at `s₁`." -/
def GJumpAt (κ : ℝ) (Gn : ℂ → ℂ) (α s₁ : ℂ) : Prop :=
  ∀ ρ : ℝ, ∀ F : ℂ → ℂ, 0 < ρ → IsCutDisc κ α s₁ ρ → AnalyticOnNhd ℂ F (ball s₁ ρ) →
    EqOn F Gn (upperPart κ α s₁ ρ) → EqOn F (fun s => Gn s + Mon α s) (lowerPart κ α s₁ ρ)

/-- One witness disc containing `s₁` gives the jump for every cut disc at `s₁`. -/
theorem G_jumpAt_of_witness {κ : ℝ} {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn) {α : ℂ}
    (hα : α ∈ catalogue) {s' s₁ : ℂ} (h' : ((s' - α) / slantDir κ).im = 0)
    (hs₁ : s₁ ∈ cut (slantDir κ) α) {ρ' : ℝ} {F' : ℂ → ℂ}
    (hF' : AnalyticOnNhd ℂ F' (ball s' ρ')) (hup' : EqOn F' Gn (upperPart κ α s' ρ'))
    (hjump' : EqOn F' (fun s => Gn s + Mon α s) (lowerPart κ α s' ρ'))
    (hmem : s₁ ∈ ball s' ρ') : GJumpAt κ Gn α s₁ := by
  intro ρ F hρ hD hF hup
  exact G_jump_transfer hP hα h' hs₁ hD hF' hF hup' hup hjump' ⟨s₁, hmem, mem_ball_self hρ⟩

/-- Step (2): the jump near `α`, from the local form. -/
theorem G_jump_near {κ : ℝ} {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn) {α : ℂ}
    (hα : α ∈ catalogue) :
    ∃ t ∈ Ioo (0 : ℝ) (α.re - 1), GJumpAt κ Gn α (α - (t : ℂ) * slantDir κ) := by
  obtain ⟨rα, hrα, hrα1, -, H, hH, hEq⟩ := hP.local_form α hα
  have hv := slantDir_ne_zero κ
  have hnv1 := G_one_le_norm_slantDir κ
  have hnv : 0 < ‖slantDir κ‖ := by linarith
  set t₁ : ℝ := rα / (2 * ‖slantDir κ‖) with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁v : t₁ * ‖slantDir κ‖ = rα / 2 := by rw [ht₁]; field_simp
  have ht₁1 : t₁ < α.re - 1 := by
    have : t₁ ≤ t₁ * ‖slantDir κ‖ := le_mul_of_one_le_right ht₁0.le hnv1
    linarith
  set s₁ := α - (t₁ : ℂ) * slantDir κ with hs₁def
  have hs₁ : s₁ ∈ cut (slantDir κ) α := ⟨t₁, ht₁0.le, ht₁1, rfl⟩
  have hne₁ : s₁ ≠ α := by
    intro h
    have : (t₁ : ℂ) * slantDir κ = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ht₁0.ne' (by exact_mod_cast h')
    · exact hv h'
  have hdist₁ : dist s₁ α = rα / 2 := by
    rw [dist_eq_norm, hs₁def, show α - (t₁ : ℂ) * slantDir κ - α = -((t₁ : ℂ) * slantDir κ) by ring,
      norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₁0, ht₁v]
  obtain ⟨ρ₁, hρ₁, hD₁, F₁, hF₁, hup₁⟩ := hP.access α hα s₁ hs₁ hne₁
  set ρ : ℝ := min ρ₁ (rα / 2) with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (by positivity)
  have hD : IsCutDisc κ α s₁ ρ := hD₁.mono (min_le_left _ _)
  have hballα : ball s₁ ρ ⊆ ball α rα := by
    intro s hs
    rw [mem_ball] at hs ⊢
    have := dist_triangle s s₁ α
    have : ρ ≤ rα / 2 := min_le_right _ _
    linarith
  have hsub : ball s₁ ρ ⊆ ball s₁ ρ₁ := ball_subset_ball (min_le_left _ _)
  -- the continuation of the local form from the `+` side
  set K : ℂ → ℂ := fun s =>
    X α s * (Complex.log (-((s - α) / slantDir κ)) + Real.pi * I) + H s with hK
  have hslit : ∀ s ∈ ball s₁ ρ, -((s - α) / slantDir κ) ∈ slitPlane := by
    intro s hs
    rw [Complex.mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    set w := (s - α) / slantDir κ with hw
    have hwre : 0 ≤ w.re := by simp at hre; linarith
    have hwim : w.im = 0 := by simpa using him
    have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hwim])
    have hse : s = α + (w.re : ℂ) * slantDir κ := by
      have : w * slantDir κ = s - α := by rw [hw]; field_simp
      rw [hwr] at this; linear_combination -this
    have hds : dist s s₁ = (w.re + t₁) * ‖slantDir κ‖ := by
      rw [dist_eq_norm, hse, hs₁def,
        show α + (w.re : ℂ) * slantDir κ - (α - (t₁ : ℂ) * slantDir κ) =
          ((w.re + t₁ : ℝ) : ℂ) * slantDir κ by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hdα : dist α s₁ ≤ dist s s₁ := by
      rw [dist_comm, hdist₁, hds, ← ht₁v]
      nlinarith
    exact hD.2.1 (mem_ball.mpr (lt_of_le_of_lt hdα (mem_ball.mp hs)))
  have hXa : AnalyticOnNhd ℂ (X α) HH :=
    (X_differentiableOn hα).analyticOnNhd (isOpen_halfPlane 1)
  have hKa : AnalyticOnNhd ℂ K (ball s₁ ρ) := by
    intro s hs
    refine ((hXa s (hD.1 hs)).mul ?_).add (hH s (hballα hs))
    refine AnalyticAt.add ?_ analyticAt_const
    exact (by fun_prop : AnalyticAt ℂ (fun s => -((s - α) / slantDir κ)) s).clog (hslit s hs)
  -- points off the line inside the small disc lie in the slit disc
  have hslitD : ∀ s ∈ ball s₁ ρ, ((s - α) / slantDir κ).im ≠ 0 →
      s ∈ slitDisc (slantDir κ) α rα :=
    fun s hs him => ⟨hballα hs, fun hc => him (G_im_cut hc)⟩
  have hupK : EqOn F₁ K (upperPart κ α s₁ ρ) := by
    intro s hs
    rw [hup₁ ⟨hsub hs.1, hs.2⟩, hEq (hslitD s hs.1 hs.2.ne'), hK]
    simp only [logAt]
    rw [G_log_upper hs.2]
  obtain ⟨⟨zu, hzuO, hzu⟩, -⟩ := G_exists_upper_lower (κ := κ) (α := α) isOpen_ball
    (mem_ball_self hρ) (G_im_cut hs₁)
  obtain ⟨-, -, -, hupo, -, -, -⟩ := cutDisc_facts hs₁ hD
  have hFK : EqOn F₁ K (ball s₁ ρ) :=
    G_eqOn_of_subset (hF₁.mono hsub) hKa (convex_ball _ _).isPreconnected hupo
      (fun z hz => hz.1) ⟨hzuO, hzu⟩ hupK
  have hjump : EqOn F₁ (fun s => Gn s + Mon α s) (lowerPart κ α s₁ ρ) := by
    intro s hs
    show F₁ s = Gn s + Mon α s
    rw [hFK hs.1, hEq (hslitD s hs.1 hs.2.ne), hK]
    simp only [logAt, Mon]
    rw [G_log_lower hs.2]
    ring
  refine ⟨t₁, ⟨ht₁0, ht₁1⟩, ?_⟩
  exact G_jumpAt_of_witness hP hα (G_im_cut hs₁) hs₁ (hF₁.mono hsub)
    (fun s hs => hup₁ ⟨hsub hs.1, hs.2⟩) hjump (mem_ball_self hρ)

/-- **the jump corollary** (in the one-sided form used by the branch proposition): any continuation of `Gn`
from the `+` side across `s₀ ∈ cut_α` equals `Gn + M_α` on the `-` side. No RH.

Sketch. Only `G⁺` is needed, not `G⁺ - G⁻`. Let `T` be the set of `t ∈ (0, Re α - 1)`
such that at `s_t = α - tv` the jump holds for *every* `(r', Gp')` as in the statement with `r'` small
(say `r' ≤ r_t`, `r_t` from `hP.access`). (1) Near `α`: by `hP.local_form`, `Gn = X Log_α + H` on the
slit disc; for `s_t` in that disc and `Gp'` analytic on a ball inside it with `Gp' = Gn` on the `+`
part, `Gp' = X·L⁺ + H` on the ball (identity theorem on the convex ball, `L⁺(w) = Log(-w) + iπ` the
continuation of `Log` from `Im > 0`, here `w = (s-α)/v`), and `L⁺ = Log + 2πi` on `Im w < 0`. So small
`t` lie in `T`. (2) `T` is open and closed in `(0, Re α - 1)`: two access discs whose centres are
close overlap in a convex set meeting both sides (`cutDisc_facts`); the two continuations agree on
the `+` part of the overlap, hence on the overlap (identity theorem), so the jump transfers. (3)
Connectedness gives `T = (0, Re α - 1)`; for the given `(r, Gp)` the jump holds near `s₀` on the `-`
side, hence on all of the convex `V⁻` (identity theorem; `Gn` analytic on `V⁻ ⊆ Ω_ℍ`, `Mon α` on
`ℍ`, `Mon_analyticOn`). -/
theorem jump_of_access {κ : ℝ} (hκ : IsGoodSlant κ) {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn)
    {α : ℂ} (hα : α ∈ catalogue) {s₀ : ℂ} (hs₀ : s₀ ∈ cut (slantDir κ) α) (hne : s₀ ≠ α)
    {r : ℝ} (hr : 0 < r) (hD : IsCutDisc κ α s₀ r) {Gp : ℂ → ℂ}
    (hGp : AnalyticOnNhd ℂ Gp (ball s₀ r)) (hup : EqOn Gp Gn (upperPart κ α s₀ r)) :
    EqOn Gp (fun s => Gn s + Mon α s) (lowerPart κ α s₀ r) := by
  have hv := slantDir_ne_zero κ
  have hnv : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hv
  set c : ℝ → ℂ := fun t => α - (t : ℂ) * slantDir κ with hc
  set I₀ : Set ℝ := Ioo (0 : ℝ) (α.re - 1) with hI₀
  have hcut : ∀ t ∈ I₀, c t ∈ cut (slantDir κ) α := fun t ht => ⟨t, ht.1.le, ht.2, rfl⟩
  have hcne : ∀ t ∈ I₀, c t ≠ α := by
    intro t ht h
    have : (t : ℂ) * slantDir κ = 0 := by simp only [hc] at h; linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ht.1.ne' (by exact_mod_cast h')
    · exact hv h'
  have hcdist : ∀ x y : ℝ, dist (c y) (c x) = |y - x| * ‖slantDir κ‖ := by
    intro x y
    rw [dist_eq_norm, hc, show α - (y : ℂ) * slantDir κ - (α - (x : ℂ) * slantDir κ) =
      -(((y - x : ℝ) : ℂ) * slantDir κ) by push_cast; ring, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
  -- local constancy of `GJumpAt` along the cut
  have hloc : ∀ x ∈ I₀, ∀ᶠ y in 𝓝[I₀] x,
      (GJumpAt κ Gn α (c x) ↔ GJumpAt κ Gn α (c y)) := by
    intro x hx
    obtain ⟨ρ₁, hρ₁, hD₁, F₁, hF₁, hup₁⟩ := hP.access α hα (c x) (hcut x hx) (hcne x hx)
    have hnear : ∀ᶠ y in 𝓝 x, |y - x| < ρ₁ / ‖slantDir κ‖ := by
      have : ∀ᶠ y in 𝓝 x, dist y x < ρ₁ / ‖slantDir κ‖ :=
        Metric.eventually_nhds_iff.mpr ⟨ρ₁ / ‖slantDir κ‖, by positivity, fun _ h => h⟩
      simpa [Real.dist_eq] using this
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with y hy hyI
    have hmem : c y ∈ ball (c x) ρ₁ := by
      rw [mem_ball, hcdist]
      rwa [lt_div_iff₀ hnv] at hy
    constructor
    · intro hJx
      have hj₁ := hJx ρ₁ F₁ hρ₁ hD₁ hF₁ hup₁
      exact G_jumpAt_of_witness hP hα (G_im_cut (hcut x hx)) (hcut y hyI) hF₁ hup₁ hj₁ hmem
    · intro hJy
      obtain ⟨ρ₂, hρ₂, hD₂, F₂, hF₂, hup₂⟩ := hP.access α hα (c y) (hcut y hyI) (hcne y hyI)
      have hj₂ := hJy ρ₂ F₂ hρ₂ hD₂ hF₂ hup₂
      have hj₁ := G_jump_transfer hP hα (G_im_cut (hcut y hyI)) (hcut x hx) hD₁ hF₂ hF₁ hup₂ hup₁
        hj₂ ⟨c y, mem_ball_self hρ₂, hmem⟩
      exact G_jumpAt_of_witness hP hα (G_im_cut (hcut x hx)) (hcut x hx) hF₁ hup₁ hj₁
        (mem_ball_self hρ₁)
  obtain ⟨t₁, ht₁, hJ₁⟩ := G_jump_near hP hα
  obtain ⟨t₀, ht₀, ht₀1, rfl⟩ := hs₀
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hne
  have hall := (isPreconnected_Ioo (a := (0 : ℝ)) (b := α.re - 1)).induction₂
    (fun x y => GJumpAt κ Gn α (c x) ↔ GJumpAt κ Gn α (c y)) hloc
    (fun _ _ _ _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ _ h => h.symm) ht₁ ⟨ht₀pos, ht₀1⟩
  exact (hall.mp hJ₁) r Gp hr hD hGp hup

end GoldbachBoundaries.ThmA
