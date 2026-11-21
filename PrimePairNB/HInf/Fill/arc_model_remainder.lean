import PrimePairNB.HInf.Fill.arc_model_extension
import PrimePairNB.HInf.Fill.arc_model_residue

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

def arc_model_avg (f : ℂ → ℂ → ℂ) (ε μ : ℂ) : ℂ :=
  ∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * ε) μ

def arc_model_east (r₀ : ℝ) (f : ℂ → ℂ → ℂ) (ε μ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    (ThmA.segInt (fun t => f t μ * Complex.log t / (ε - t))
      ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) +
    ThmA.segInt (fun t => f t μ * Complex.log t / (ε - t))
      ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I))

lemma arc_model_scale_mem {r : ℝ} {ε : ℂ} (hε : ε ∈ ball (0 : ℂ) r)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : (τ : ℂ) * ε ∈ ball (0 : ℂ) r := by
  rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  exact (mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg ε)).trans_lt
    (by simpa using mem_ball_zero_iff.mp hε)

lemma arc_model_segInt_continuous {X : Type*} [MetricSpace X] [ProperSpace X]
    {S : Set X} (hS : IsOpen S) {a b : ℂ} {A : ℂ → X → ℂ}
    (hc : ContinuousOn (fun p : X × ℂ => A p.2 p.1) (S ×ˢ segment ℝ a b)) :
    ContinuousOn (fun x => ThmA.segInt (fun t => A t x) a b) S := by
  apply ContinuousOn.const_mul
  apply arc_model_continuous_integral hS
  apply hc.comp (f := fun p : X × ℝ => (p.1, a + (p.2 : ℂ) * (b - a))) (by fun_prop)
  intro p hp
  refine ⟨hp.1, ?_⟩
  simpa only [Complex.real_smul] using (convex_segment a b).add_smul_sub_mem
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) (by simpa using hp.2)

theorem arc_model_remainder_continuous {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀))) :
    ContinuousOn (fun p : ℂ × ℂ => arc_model_east r₀ f p.1 p.2 - arc_model_avg f p.1 p.2)
      (ball (0 : ℂ) (r₀ / 8) ×ˢ ball (0 : ℂ) (r₀ / 8)) := by
  let S : Set (ℂ × ℂ) := ball (0 : ℂ) (r₀ / 8) ×ˢ ball (0 : ℂ) (r₀ / 8)
  have hS : IsOpen S := isOpen_ball.prod isOpen_ball
  have he (z : ℂ) (hz : z ∈ ball (0 : ℂ) (r₀ / 8)) : z ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz).trans (by linarith))
  have havg : ContinuousOn (fun p : ℂ × ℂ => arc_model_avg f p.1 p.2) S := by
    apply arc_model_continuous_integral hS
    apply hf.continuousOn.comp (f := fun p : (ℂ × ℂ) × ℝ => ((p.2 : ℂ) * p.1.1, p.1.2)) (by fun_prop)
    intro p hp
    exact ⟨arc_model_scale_mem (he _ hp.1.1) (by simpa using hp.2), he _ hp.1.2⟩
  have hseg {a b : ℂ}
      (hs : segment ℝ a b ⊆ segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ∪
        segment ℝ ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I)) :
      ContinuousOn (fun p : ℂ × ℂ => ThmA.segInt
        (fun t => f t p.2 * Complex.log t / (p.1 - t)) a b) S := by
    apply arc_model_segInt_continuous hS
    intro p hp
    have ht : p.2 ∈ ball (0 : ℂ) (7 * r₀ / 4) ∩ slitPlane := by
      rcases hs hp.2 with ht | ht
      · exact (east_polygon_subset hr₀).1 ht
      · exact (east_polygon_subset hr₀).2 ht
    have ht' : p.2 ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ht.1).trans (by linarith))
    have hn : p.1.1 - p.2 ≠ 0 := by
      have hh := east_polygon_right_slit hr₀
        ((mem_ball_zero_iff.mp hp.1.1).trans (by linarith)) p.2 (hs hp.2)
      exact sub_ne_zero.mpr (sub_ne_zero.mp (slitPlane_ne_zero hh)).symm
    have hc := (hf.differentiableAt (x := (p.2, p.1.2)) ((isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨ht', he _ hp.1.2⟩)).continuousAt.comp
        (f := fun p : (ℂ × ℂ) × ℂ => (p.2, p.1.2))
        (show ContinuousAt (fun p : (ℂ × ℂ) × ℂ => (p.2, p.1.2)) p by fun_prop)
    exact ((hc.mul ((Complex.hasDerivAt_log ht.2).continuousAt.comp continuous_snd.continuousAt)).div
      (by fun_prop) hn).continuousWithinAt
  exact ((hseg (fun _ ht => Or.inl ht)).add
    (hseg (fun _ ht => Or.inr ht))).const_mul _ |>.sub havg

/-- The regular derivative is holomorphic after any affine change of its two parameters. -/
theorem arc_model_remainder_comp {r₀ R : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀)))
    {a b : ℂ → ℂ} (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (hm : ∀ z ∈ ball (0 : ℂ) R, (a z, b z) ∈
      ball (0 : ℂ) (r₀ / 8) ×ˢ ball (0 : ℂ) (r₀ / 8)) :
    DifferentiableOn ℂ (fun z => arc_model_east r₀ f (a z) (b z) - arc_model_avg f (a z) (b z))
      (ball 0 R) := by
  have he (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : b z ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp (hm z hz).2).trans (by linarith))
  have hscale (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      (τ : ℂ) * a z ∈ ball (0 : ℂ) (2 * r₀) :=
    arc_model_scale_mem
      (mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp (hm z hz).1).trans (by linarith))) hτ
  have havg : DifferentiableOn ℂ (fun z => arc_model_avg f (a z) (b z)) (ball 0 R) := by
    apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    · apply hf.continuousOn.comp (f := fun p : ℂ × ℝ => ((p.2 : ℂ) * a p.1, b p.1))
        ((((Complex.continuous_ofReal.comp continuous_snd).mul (ha.continuous.comp continuous_fst)).prodMk
          (hb.continuous.comp continuous_fst)).continuousOn)
      intro p hp
      exact ⟨hscale p.1 hp.1 p.2 (by simpa using hp.2), he p.1 hp.1⟩
    · intro τ hτ z hz
      exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨hscale z hz τ (by simpa using hτ), he z hz⟩)).comp z
          (((ha z).const_mul (τ : ℂ)).prodMk (hb z))).differentiableWithinAt
  let U : Set (ℂ × ℂ) := {p | p.1 ∈ ball 0 (7 * r₀ / 4) ∩ slitPlane ∧
    p.2 ∈ ball 0 R ∧ a p.2 - p.1 ≠ 0}
  have hU : IsOpen U := ((isOpen_ball.inter isOpen_slitPlane).preimage continuous_fst).inter
    ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_ne_fun ((ha.continuous.comp continuous_snd).sub continuous_fst) continuous_const))
  have hA : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => f p.1 (b p.2) * Complex.log p.1 / (a p.2 - p.1)) U := by
    intro p hp
    have ht : p.1 ∈ ball (0 : ℂ) (2 * r₀) :=
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hp.1.1).trans (by linarith))
    have hd : DifferentiableAt ℂ (fun p : ℂ × ℂ => f p.1 (b p.2)) p :=
      (hf.differentiableAt (x := (p.1, b p.2))
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ht, he p.2 hp.2.1⟩)).comp p
      (f := fun p : ℂ × ℂ => (p.1, b p.2))
      (differentiableAt_fst.prodMk ((hb p.2).comp p differentiableAt_snd))
    have hl : DifferentiableAt ℂ (fun p : ℂ × ℂ => Complex.log p.1) p :=
      (Complex.hasDerivAt_log hp.1.2).differentiableAt.comp p differentiableAt_fst
    have hden : DifferentiableAt ℂ (fun p : ℂ × ℂ => a p.2 - p.1) p :=
      ((ha p.2).comp p differentiableAt_snd).sub differentiableAt_fst
    convert! ((hd.mul hl).mul (hden.inv hp.2.2)).differentiableWithinAt using 1 <;>
      simp only [div_eq_mul_inv]
  have hseg {u v : ℂ}
      (hs : segment ℝ u v ⊆ segment ℝ ((-r₀ : ℝ) * I) ((r₀ / 2 : ℝ) : ℂ) ∪
        segment ℝ ((r₀ / 2 : ℝ) : ℂ) ((r₀ : ℂ) * I)) :
      DifferentiableOn ℂ (fun z => ThmA.segInt
        (fun t => f t (b z) * Complex.log t / (a z - t)) u v) (ball 0 R) := by
    apply AnalyticOnNhd.differentiableOn
    apply analyticOn_segInt_param hU hA
    intro t ht z hz
    have ht' : t ∈ ball (0 : ℂ) (7 * r₀ / 4) ∩ slitPlane := by
      rcases hs ht with ht | ht
      · exact (east_polygon_subset hr₀).1 ht
      · exact (east_polygon_subset hr₀).2 ht
    have hn := east_polygon_right_slit hr₀
      ((mem_ball_zero_iff.mp (hm z hz).1).trans (by linarith)) t (hs ht)
    exact ⟨ht', hz, sub_ne_zero.mpr (sub_ne_zero.mp (slitPlane_ne_zero hn)).symm⟩
  exact (((hseg (fun _ ht => Or.inl ht)).add
    (hseg (fun _ ht => Or.inr ht))).const_mul _).sub havg

end GoldbachBoundaries.HInf.Fill
