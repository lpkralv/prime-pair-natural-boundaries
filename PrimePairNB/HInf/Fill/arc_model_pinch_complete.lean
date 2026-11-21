import PrimePairNB.HInf.Fill.arc_model_base
import PrimePairNB.HInf.Fill.arc_model_remainder
import PrimePairNB.HInf.Fill.exists_arc

/-! The pinch integral minus its logarithmic segment term extends through zero. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

theorem arc_model_pinch_complete {r₀ : ℝ} (hr₀ : 0 < r₀) {f : ℂ → ℂ → ℂ}
    (hf : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.1 p.2)
      (ball (0 : ℂ) (2 * r₀) ×ˢ ball (0 : ℂ) (2 * r₀))) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 (r₀ / 8)) ∧
      ∀ ε ∈ ball (0 : ℂ) (r₀ / 8), ε ∈ slitPlane → ∀ ξ : ℝ → ℝ, IsArc r₀ ε ξ →
        arcInt r₀ ξ (fun t => f t ε * Complex.log t * Complex.log (ε - t)) =
          Complex.log ε * (ε * ∫ τ in (0 : ℝ)..1, f ((τ : ℂ) * ε) ε) + H ε := by
  obtain ⟨Φ, hΦ⟩ := arc_model_pinch_family hr₀ hf
  let g : ℂ → ℂ → ℂ := fun ε μ => arc_model_east r₀ f ε μ - arc_model_avg f ε μ
  let F : ℂ → ℂ → ℂ := fun ε μ => Φ ε μ - Complex.log ε * (ε * arc_model_avg f ε μ)
  let q : ℂ := ((r₀ / 16 : ℝ) : ℂ)
  have hhalf : r₀ / 8 / 2 = r₀ / 16 := by ring
  have hq : q ∈ ball (0 : ℂ) (r₀ / 8) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have he2 (z : ℂ) (hz : z ∈ ball (0 : ℂ) (r₀ / 8)) : z ∈ ball (0 : ℂ) (2 * r₀) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz).trans (by linarith))
  have hgp (μ : ℂ) (hμ : μ ∈ ball (0 : ℂ) (r₀ / 8)) :
      DifferentiableOn ℂ (fun ε => g ε μ) (ball 0 (r₀ / 8)) :=
    arc_model_remainder_comp hr₀ hf (by fun_prop) (by fun_prop) (fun z hz => ⟨hz, hμ⟩)
  have hgl (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : DifferentiableOn ℂ
      (fun ε => g (((r₀ / 8 / 2 : ℝ) : ℂ) + (τ : ℂ) * (ε - ((r₀ / 8 / 2 : ℝ) : ℂ))) ε)
      (ball 0 (r₀ / 8)) := by
    rw [hhalf]
    apply arc_model_remainder_comp hr₀ hf (by fun_prop) (by fun_prop)
    intro z hz
    refine ⟨?_, hz⟩
    simpa only [Complex.real_smul] using (convex_ball (0 : ℂ) (r₀ / 8)).add_smul_sub_mem hq hz hτ
  have hF (μ : ℂ) (hμ : μ ∈ ball (0 : ℂ) (r₀ / 8)) (ε : ℂ)
      (hε : ε ∈ ball (0 : ℂ) (r₀ / 8) ∩ slitPlane) : HasDerivAt (fun e => F e μ) (g ε μ) ε := by
    have he4 : ‖ε‖ < r₀ / 4 := (mem_ball_zero_iff.mp hε.1).trans (by linarith)
    obtain ⟨ξ, hξ⟩ := exists_arc hr₀ he4 hε.2
    have hd := arc_model_pinch_family_derivative hr₀ hf hΦ
      ⟨mem_ball_zero_iff.mpr he4, hε.2⟩ (he2 μ hμ) hξ
    have hg : DifferentiableOn ℂ (fun t => f t μ * Complex.log t)
        (ball 0 (7 * r₀ / 4) ∩ slitPlane) := by
      intro t ht
      have ht' : t ∈ ball (0 : ℂ) (2 * r₀) :=
        mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ht.1).trans (by linarith))
      exact (((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨ht', he2 μ hμ⟩)).comp t (show DifferentiableAt ℂ (fun t : ℂ => (t, μ)) t by fun_prop)).mul
          (Complex.hasDerivAt_log ht.2).differentiableAt).differentiableWithinAt
    have hp := arc_pole_eq_east_polygon hr₀ he4 hε.2 hξ hg
    have hc := hasDerivAt_pinch_counterterm hr₀ hf (he2 ε hε.1) (he2 μ hμ) hε.2
    convert hd.sub hc using 1
    · funext e
      rfl
    · change g ε μ = _
      rw [hp]
      dsimp [g, arc_model_east, arc_model_avg]
      ring
  have havg : DifferentiableOn ℂ (fun μ => arc_model_avg f q μ) (ball 0 (r₀ / 8)) := by
    apply ThmA.differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    · apply hf.continuousOn.comp (f := fun p : ℂ × ℝ => ((p.2 : ℂ) * q, p.1)) (by fun_prop)
      intro p hp
      exact ⟨arc_model_scale_mem (he2 q hq) (by simpa using hp.2), he2 p.1 hp.1⟩
    · intro τ hτ μ hμ
      exact ((hf.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨arc_model_scale_mem (he2 q hq) (by simpa using hτ), he2 μ hμ⟩)).comp μ
          (show DifferentiableAt ℂ (fun μ : ℂ => ((τ : ℂ) * q, μ)) μ by fun_prop)).differentiableWithinAt
  have hbase : DifferentiableOn ℂ (fun μ => F ((r₀ / 8 / 2 : ℝ) : ℂ) μ) (ball 0 (r₀ / 8)) := by
    rw [hhalf]
    exact (arc_model_pinch_base hr₀ hf hΦ).sub ((havg.const_mul q).const_mul (Complex.log q))
  obtain ⟨H, hH, hHeq⟩ := arc_model_assemble_lines (by positivity : 0 < r₀ / 8)
    (arc_model_remainder_continuous hr₀ hf) hgp hgl hF hbase
  refine ⟨H, hH, ?_⟩
  intro ε hε hs ξ hξ
  have he4 : ε ∈ ball (0 : ℂ) (r₀ / 4) :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hε).trans (by linarith))
  have heq := hΦ ε ⟨he4, hs⟩ ε (he2 ε hε) ξ hξ
  have hext := hHeq ε ⟨hε, hs⟩
  dsimp [F, arc_model_avg] at hext
  linear_combination hext - heq

end GoldbachBoundaries.HInf.Fill
