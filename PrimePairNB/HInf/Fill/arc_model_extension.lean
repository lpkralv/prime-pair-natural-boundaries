import PrimePairNB.HInf.Defs
import Mathlib.Analysis.Complex.Convex
import PrimePairNB.HInf.Fill.arc_model_mixed

/-! A version of the derivative assembly using scalar parameter integrals.
Joint continuity and holomorphy along the required affine lines suffice. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma arc_model_continuous_integral {X : Type*} [MetricSpace X] [ProperSpace X]
    {S : Set X} (hS : IsOpen S) {A : X → ℝ → ℂ} {a b : ℝ}
    (hc : ContinuousOn (Function.uncurry A) (S ×ˢ [[a, b]])) :
    ContinuousOn (fun x => ∫ t in a..b, A x t) S := by
  apply ThmA.GroupC.continuousOn_param_intervalIntegral hc
  intro x hx
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS x hx
  refine ⟨closedBall x (δ / 2), isCompact_closedBall _ _,
    (closedBall_subset_ball (by linarith)).trans hδS, ?_⟩
  exact nhdsWithin_le_nhds (closedBall_mem_nhds x (by positivity))

theorem arc_model_assemble_lines {R : ℝ} (hR : 0 < R) {F g : ℂ → ℂ → ℂ}
    (hgc : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R))
    (hgp : ∀ μ ∈ ball (0 : ℂ) R, DifferentiableOn ℂ (fun ε => g ε μ) (ball 0 R))
    (hgl : ∀ τ ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ
      (fun ε => g (((R / 2 : ℝ) : ℂ) + (τ : ℂ) * (ε - ((R / 2 : ℝ) : ℂ))) ε) (ball 0 R))
    (hF : ∀ μ ∈ ball (0 : ℂ) R, ∀ ε ∈ ball (0 : ℂ) R ∩ slitPlane,
      HasDerivAt (fun e => F e μ) (g ε μ) ε)
    (hbase : DifferentiableOn ℂ (fun μ => F ((R / 2 : ℝ) : ℂ) μ) (ball 0 R)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 R) ∧
      ∀ ε ∈ ball (0 : ℂ) R ∩ slitPlane, F ε ε = H ε := by
  let q : ℂ := ((R / 2 : ℝ) : ℂ)
  have hq : q ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hqs : q ∈ slitPlane := ofReal_mem_slitPlane.mpr (by positivity)
  have hU : IsOpen (ball (0 : ℂ) R ∩ slitPlane) := isOpen_ball.inter isOpen_slitPlane
  have hstar : StarConvex ℝ q (ball (0 : ℂ) R ∩ slitPlane) :=
    ((convex_ball (0 : ℂ) R).starConvex hq).inter
      (Complex.starConvex_ofReal_slitPlane (show 0 < R / 2 by positivity))
  have hUc : IsPreconnected (ball (0 : ℂ) R ∩ slitPlane) :=
    (hstar.isPathConnected ⟨hq, hqs⟩).isConnected.isPreconnected
  have hprim (μ : ℂ) (hμ : μ ∈ ball (0 : ℂ) R) (t : ℂ) (ht : t ∈ ball (0 : ℂ) R) :
      HasDerivAt (fun e => ThmA.segInt (fun w => g w μ) q e) (g t μ) t :=
    ThmA.GroupC.hasDerivAt_segInt isOpen_ball (convex_ball _ _) (hgp μ hμ) hq ht
  have heq (μ : ℂ) (hμ : μ ∈ ball (0 : ℂ) R) (ε : ℂ) (hε : ε ∈ ball (0 : ℂ) R ∩ slitPlane) :
      F ε μ = F q μ + ThmA.segInt (fun t => g t μ) q ε := by
    obtain ⟨C, hC⟩ := hU.exists_eq_add_of_deriv_eq hUc
      (fun e he => (hF μ hμ e he).differentiableAt.differentiableWithinAt)
      (fun e he => (hprim μ hμ e he.1).differentiableAt.differentiableWithinAt)
      (fun e he => by rw [(hF μ hμ e he).deriv, (hprim μ hμ e he.1).deriv])
    have hCq := hC ⟨hq, hqs⟩
    have hCe := hC hε
    simp only [ThmA.segInt, sub_self, zero_mul] at hCq
    linear_combination hCe - hCq
  refine ⟨fun ε => F q ε + ThmA.segInt (fun t => g t ε) q ε, ?_,
    fun ε hε => heq ε hε.1 ε hε⟩
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply hbase.add
  have hd : DifferentiableOn ℂ (fun ε => ∫ τ in (0 : ℝ)..1, g (q + (τ : ℂ) * (ε - q)) ε)
      (ball 0 R) := by
    apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    · apply hgc.comp (f := fun p : ℂ × ℝ => (q + (p.2 : ℂ) * (p.1 - q), p.1)) (by fun_prop)
      intro p hp
      refine ⟨?_, hp.1⟩
      simpa only [Complex.real_smul] using (convex_ball (0 : ℂ) R).add_smul_sub_mem
        hq hp.1 (by simpa using hp.2)
    · intro τ hτ
      exact hgl τ (by simpa using hτ)
  exact (by fun_prop : DifferentiableOn ℂ (fun ε : ℂ => ε - q) (ball 0 R)).mul hd

end GoldbachBoundaries.HInf.Fill
