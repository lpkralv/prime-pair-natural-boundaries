import PrimePairNB.HInf.MixSheet
import PrimePairNB.HInf.Fill.local_model

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

lemma scaled_Pth {κ : ℝ} (hκ : IsGenericSlope κ) {a : ℂ} (ha : a ∈ PoleSetQ) :
    ∃ q : ℝ, 0 < q ∧ ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball 0 (2 * q)) ∧
      ∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Pth κ (a + t * slantDir κ) = cP a * Complex.log t + E t := by
  obtain ⟨R, hR, -, -, E, hE, he⟩ := Pth_local ha (fun b hb hba => hκ.1 b hb a ha hba)
  have hw := ThmA.slantDir_ne_zero κ
  have hn : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hw
  let q := R / (4 * ‖slantDir κ‖)
  have hq : 0 < q := by dsimp [q]; positivity
  have hm (t : ℂ) (ht : t ∈ ball (0 : ℂ) (2 * q)) : a + t * slantDir κ ∈ ball a R := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul]
    have ht' := mem_ball_zero_iff.mp ht
    have heq : 2 * q * ‖slantDir κ‖ = R / 2 := by dsimp [q]; field_simp; ring
    have := mul_lt_mul_of_pos_right ht' hn
    rw [heq] at this
    linarith
  refine ⟨q, hq, fun t => cP a * Complex.log (slantDir κ) + E (a + t * slantDir κ), ?_, ?_⟩
  · intro t ht
    exact analyticAt_const.add (AnalyticAt.comp (f := fun t : ℂ => a + t * slantDir κ)
      (hE _ (hm t ht)) (by fun_prop))
  · intro t ht hs
    have hr : a + t * slantDir κ ∉ rayW κ a := by
      rw [not_mem_rayW_iff]
      simpa [hw] using hs
    rw [he _ ⟨hm t ht, hr⟩]
    simp only [logK, add_sub_cancel_left, mul_div_cancel_right₀ _ hw]
    ring

lemma scaled_kernel (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} {x a : ℂ} (hxV : x ∈ Vt ⊤)
    (ha : a ∈ collide x) :
    ∃ q : ℝ, 0 < q ∧ DifferentiableOn ℂ
      (fun p : ℂ × ℂ => slantDir κ * kerG (a + p.1 * slantDir κ) (x + p.2 * slantDir κ))
      (ball (0 : ℂ) (2 * q) ×ˢ ball (0 : ℂ) (2 * q)) := by
  let g : ℂ × ℂ → ℂ × ℂ := fun p => (a + p.1 * slantDir κ, x + p.2 * slantDir κ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hmem : g (0, 0) ∈ domK ⊤ := by
    have hb := (M1.poleSetQ_re_bounds ha.2).1
    refine ⟨by simpa [g] using hxV, ?_, ?_⟩
    · simpa [g] using (M1.poleSetQ_re_bounds ha.1).1
    · simpa [g, sub_re] using hb
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp ((isOpen_domK ⊤).preimage hg) (0, 0) hmem
  refine ⟨R / 4, by positivity, ?_⟩
  refine DifferentiableOn.const_mul (hK.holo.comp (f := g) (by dsimp [g]; fun_prop) ?_) _
  rintro ⟨t, ε⟩ ⟨ht, hε⟩
  apply hball
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_ball.mp ht).trans (by linarith), (mem_ball.mp hε).trans (by linarith)⟩

lemma scaled_Qcont {κ : ℝ} {b : ℂ} (hb : b ∈ PoleSetQ) :
    ∃ q : ℝ, 0 < q ∧ ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball 0 (2 * q)) ∧
      ∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Qcont (b + t * slantDir κ) = (Rcoef b / slantDir κ) / t + E t := by
  obtain ⟨g, hg, heq⟩ := Fill.exists_regular_part hb
  have heq' : ∀ᶠ z in 𝓝 b, z ≠ b → g z = Qcont z - Rcoef b / (z - b) :=
    eventually_nhdsWithin_iff.mp heq
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hg.eventually_analyticAt.and heq')
  have hw := ThmA.slantDir_ne_zero κ
  have hn : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hw
  let q := R / (4 * ‖slantDir κ‖)
  have hq : 0 < q := by dsimp [q]; positivity
  have hm (t : ℂ) (ht : t ∈ ball (0 : ℂ) (2 * q)) : b + t * slantDir κ ∈ ball b R := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul]
    have ht' := mem_ball_zero_iff.mp ht
    have he : 2 * q * ‖slantDir κ‖ = R / 2 := by dsimp [q]; field_simp; ring
    have := mul_lt_mul_of_pos_right ht' hn
    rw [he] at this
    linarith
  refine ⟨q, hq, fun t => g (b + t * slantDir κ), ?_, ?_⟩
  · intro t ht
    exact AnalyticAt.comp (f := fun t : ℂ => b + t * slantDir κ)
      (hball _ (hm t ht)).1 (by fun_prop)
  · intro t ht hs
    have ht0 := slitPlane_ne_zero hs
    have hz : b + t * slantDir κ ≠ b := by
      simpa using mul_ne_zero ht0 hw
    have he := (hball _ (hm t ht)).2 hz
    simp only [add_sub_cancel_left] at he
    have hf : Rcoef b / slantDir κ / t = Rcoef b / (t * slantDir κ) := by ring
    rw [hf]
    linear_combination -he

lemma local_arc_data (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ}
    (hκ : IsGenericSlope κ) {x : ℂ} (hxV : x ∈ Vt ⊤) (a : collide x) :
    ∃ q : ℝ, 0 < q ∧ ∃ E₁ E₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ E₁ (ball 0 (2 * q)) ∧ AnalyticOnNhd ℂ E₂ (ball 0 (2 * q)) ∧
      DifferentiableOn ℂ
        (fun p : ℂ × ℂ => slantDir κ * kerG (a + p.1 * slantDir κ) (x + p.2 * slantDir κ))
        (ball (0 : ℂ) (2 * q) ×ˢ ball (0 : ℂ) (2 * q)) ∧
      (∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Pth κ (a + t * slantDir κ) = cP a * Complex.log t + E₁ t) ∧
      (∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Qcont (x - a + t * slantDir κ) =
          (Rcoef (x - a) / slantDir κ) / t + E₂ t) := by
  obtain ⟨q₁, hq₁, E₁, hE₁, he₁⟩ := scaled_Pth hκ a.property.1
  obtain ⟨q₂, hq₂, E₂, hE₂, he₂⟩ := scaled_Qcont (κ := κ) a.property.2
  obtain ⟨q₃, hq₃, hf⟩ := scaled_kernel hK hxV a.property
  let q := min q₁ (min q₂ q₃)
  have hq1 : q ≤ q₁ := min_le_left _ _
  have hq2 : q ≤ q₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : q ≤ q₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hm1 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₁) := ball_subset_ball (by linarith)
  have hm2 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₂) := ball_subset_ball (by linarith)
  have hm3 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₃) := ball_subset_ball (by linarith)
  exact ⟨q, lt_min hq₁ (lt_min hq₂ hq₃), E₁, E₂, hE₁.mono hm1, hE₂.mono hm2,
    hf.mono (Set.prod_mono hm3 hm3), (fun t ht => he₁ t (hm1 ht)), (fun t ht => he₂ t (hm2 ht))⟩

end GoldbachBoundaries.HInf.MixProof
