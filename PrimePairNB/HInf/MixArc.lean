import PrimePairNB.HInf.Fill.arc_model

/-! The local log–pole arc, retaining the kernel at the moving pole. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

def poleEast (r : ℝ) (g : ℂ → ℂ → ℂ) (ε : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    (ThmA.segInt (fun t => g t ε / (ε - t)) ((-r : ℝ) * I) ((r / 2 : ℝ) : ℂ) +
      ThmA.segInt (fun t => g t ε / (ε - t)) ((r / 2 : ℝ) : ℂ) ((r : ℂ) * I))

lemma poleEast_analytic {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ → ℂ}
    (hg : DifferentiableOn ℂ (fun p : ℂ × ℂ => g p.1 p.2)
      ((ball (0 : ℂ) (7 * r / 4) ∩ slitPlane) ×ˢ ball (0 : ℂ) (r / 4))) :
    AnalyticOnNhd ℂ (poleEast r g) (ball 0 (r / 8)) := by
  let U : Set (ℂ × ℂ) := {p | p.1 ∈ ball 0 (7 * r / 4) ∩ slitPlane ∧
    p.2 ∈ ball 0 (r / 8) ∧ p.2 - p.1 ≠ 0}
  have hU : IsOpen U := ((isOpen_ball.inter isOpen_slitPlane).preimage continuous_fst).inter
    ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_ne_fun (continuous_snd.sub continuous_fst) continuous_const))
  have hA : DifferentiableOn ℂ (fun p : ℂ × ℂ => g p.1 p.2 / (p.2 - p.1)) U := by
    intro p hp
    have hp2 : p.2 ∈ ball (0 : ℂ) (r / 4) :=
      ball_subset_ball (by linarith) hp.2.1
    have hdg := hg.differentiableAt (((isOpen_ball.inter isOpen_slitPlane).prod isOpen_ball).mem_nhds
      ⟨hp.1, hp2⟩)
    have hden : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2 - p.1) p := by fun_prop
    convert (hdg.mul (hden.inv hp.2.2)).differentiableWithinAt using 1 <;>
      simp only [div_eq_mul_inv] <;> rfl
  have hseg {a b : ℂ}
      (hs : segment ℝ a b ⊆ segment ℝ ((-r : ℝ) * I) ((r / 2 : ℝ) : ℂ) ∪
        segment ℝ ((r / 2 : ℝ) : ℂ) ((r : ℂ) * I)) :
      AnalyticOnNhd ℂ (fun ε => ThmA.segInt (fun t => g t ε / (ε - t)) a b)
        (ball 0 (r / 8)) := by
    apply analyticOn_segInt_param hU hA
    intro t ht ε hε
    have ht' : t ∈ ball (0 : ℂ) (7 * r / 4) ∩ slitPlane := by
      rcases hs ht with h | h
      · exact (east_polygon_subset hr).1 h
      · exact (east_polygon_subset hr).2 h
    have hn := east_polygon_right_slit hr
      ((mem_ball_zero_iff.mp hε).trans (by linarith)) t (hs ht)
    exact ⟨ht', hε, sub_ne_zero.mpr (sub_ne_zero.mp (slitPlane_ne_zero hn)).symm⟩
  exact fun ε hε => analyticAt_const.mul
    ((hseg (fun _ ht => Or.inl ht) ε hε).add (hseg (fun _ ht => Or.inr ht) ε hε))

theorem arc_model_mix {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {E₁ E₂ : ℂ → ℂ} (hE₁ : AnalyticOnNhd ℂ E₁ (ball 0 (2 * r₀)))
    (hE₂ : AnalyticOnNhd ℂ E₂ (ball 0 (2 * r₀))) (ca cb : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ / 4 ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 r) ∧
      ∀ ε ∈ ball (0 : ℂ) r, ε ∈ slitPlane → ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * (ca * Complex.log t + E₁ t) *
          (cb / (ε - t) + E₂ (ε - t))) =
          ca * cb * Complex.log ε * f ε ε + H ε := by
  let g : ℂ → ℂ → ℂ := fun t ε => f t ε * (ca * Complex.log t + E₁ t)
  have hg : DifferentiableOn ℂ (fun p : ℂ × ℂ => g p.1 p.2)
      ((ball (0 : ℂ) (7 * r₀ / 4) ∩ slitPlane) ×ˢ ball (0 : ℂ) (r₀ / 4)) := by
    intro p hp
    have ht : p.1 ∈ ball (0 : ℂ) (2 * r₀) := ball_subset_ball (by linarith) hp.1.1
    have he : p.2 ∈ ball (0 : ℂ) (2 * r₀) := ball_subset_ball (by linarith) hp.2
    exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht, he⟩)).mul
      (((Complex.hasDerivAt_log hp.1.2).differentiableAt.comp p differentiableAt_fst |>.const_mul ca).add
        ((hE₁ _ ht).differentiableAt.comp p differentiableAt_fst))).differentiableWithinAt
  have hEast := poleEast_analytic hr₀ hg
  obtain ⟨HL, hHL, hL⟩ := arc_model_mixed_left hr₀ hf hE₂
  obtain ⟨HB, hHB, hB⟩ := arc_model_regular hr₀ hf hE₁ hE₂
  let H : ℂ → ℂ := fun ε => cb * (f ε ε * E₁ ε + poleEast r₀ g ε) + ca * HL ε + HB ε
  have he8 (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) (r₀ / 16)) : ε ∈ ball (0 : ℂ) (r₀ / 8) :=
    ball_subset_ball (by linarith) hε
  have he4 (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) (r₀ / 16)) : ε ∈ ball (0 : ℂ) (r₀ / 4) :=
    ball_subset_ball (by linarith) hε
  have he2 (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) (r₀ / 16)) : ε ∈ ball (0 : ℂ) (2 * r₀) :=
    ball_subset_ball (by linarith) hε
  refine ⟨r₀ / 16, by positivity, by linarith, H, ?_, ?_⟩
  · intro ε hε
    have hdiag : DifferentiableOn ℂ (fun z => f z z) (ball 0 (r₀ / 16)) :=
      hf.comp (f := fun z : ℂ => (z, z)) (by fun_prop)
        (fun z hz => ⟨he2 z hz, he2 z hz⟩)
    have hd : AnalyticAt ℂ (fun z => f z z) ε := hdiag.analyticOnNhd isOpen_ball ε hε
    exact ((analyticAt_const.mul (((hd.mul (hE₁ ε (he2 ε hε))).add
      (hEast ε (he8 ε hε))))).add (analyticAt_const.mul (hHL ε (he4 ε hε)))).add
        (hHB ε (he4 ε hε))
  · intro ε hε hs ξ hξ
    have hgp : DifferentiableOn ℂ (fun t => g t ε)
        (ball 0 (7 * r₀ / 4) ∩ slitPlane) :=
      hg.comp (f := fun t : ℂ => (t, ε)) (by fun_prop) (fun _ ht => ⟨ht, he4 ε hε⟩)
    have hp := arc_pole_eq_east_polygon hr₀ (mem_ball_zero_iff.mp (he4 ε hε)) hs hξ hgp
    have hpt := arcPt_continuousOn hξ
    have htm (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((hξ.small h hh).trans (by linarith))
    have hum (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) : ε - arcPt ξ h ∈ ball (0 : ℂ) (2 * r₀) := by
      rw [mem_ball_zero_iff]
      have ht : ‖arcPt ξ h‖ < 3 * r₀ / 2 := hξ.small h hh
      exact (norm_sub_le ε _).trans_lt (by linarith [mem_ball_zero_iff.mp hε])
    have hfc : ContinuousOn (fun h => f (arcPt ξ h) ε) (Icc (-r₀) r₀) :=
      hf.continuousOn.comp (hpt.prodMk continuousOn_const) (fun h hh => ⟨htm h hh, he2 ε hε⟩)
    have hlog := hpt.clog (fun h _ => (arcPt_slit hξ h).1)
    have hcE₁ := hE₁.continuousOn.comp hpt htm
    have hcE₂ := hE₂.continuousOn.comp (continuousOn_const.sub hpt) hum
    let P : ℂ → ℂ := fun t => g t ε / (ε - t)
    let L : ℂ → ℂ := fun t => f t ε * Complex.log t * E₂ (ε - t)
    let B : ℂ → ℂ := fun t => f t ε * E₁ t * E₂ (ε - t)
    have hcP : ContinuousOn (fun h => P (arcPt ξ h)) (Icc (-r₀) r₀) :=
      (hfc.mul ((hlog.const_mul ca).add hcE₁)).div (continuousOn_const.sub hpt)
        (fun h _ => slitPlane_ne_zero (arcPt_slit hξ h).2)
    have hcL : ContinuousOn (fun h => L (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hlog).mul hcE₂
    have hcB : ContinuousOn (fun h => B (arcPt ξ h)) (Icc (-r₀) r₀) := (hfc.mul hcE₁).mul hcE₂
    have hexpand : (fun t => f t ε * (ca * Complex.log t + E₁ t) *
        (cb / (ε - t) + E₂ (ε - t))) = (fun t => (cb * P t + ca * L t) + B t) := by
      funext t
      dsimp [P, L, B, g]
      ring
    rw [hexpand, arc_model_arcInt_add hr₀ hξ ((hcP.const_mul cb).add (hcL.const_mul ca)) hcB,
      arc_model_arcInt_add hr₀ hξ (hcP.const_mul cb) (hcL.const_mul ca),
      arc_model_arcInt_const_mul, arc_model_arcInt_const_mul]
    change cb * arcInt r₀ ξ (fun t => g t ε / (ε - t)) +
      ca * arcInt r₀ ξ L + arcInt r₀ ξ B = _
    rw [hp, hL ε (he4 ε hε) ξ hξ, hB ε (he4 ε hε) ξ hξ]
    dsimp [H, poleEast, g]
    ring

end GoldbachBoundaries.HInf.MixProof
