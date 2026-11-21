import PrimePairNB.Paper2.M1.Kernel

/-!
# `norm_KerS_mul_pow_le`

`|Γ(w)| (1 + |Im w|)^n` is bounded on the strip (the RH development's `norm_Gamma_mul_one_add_abs_im_pow_le`),
`|Γ(s - w)|` is bounded on the strip `σ₁ - x₂ ≤ Re ≤ σ₂ - x₁` (same lemma with `n = 0`), and `1/Γ` is
continuous (entire), hence bounded on the compact rectangle of `s`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Kernel bound** (with polynomial decay of every order in place of the paper's `e^{-π|y|}`):
for `0 < x₁`, `x₂ < σ₁`, uniformly for `s` in the rectangle `σ₁ ≤ σ ≤ σ₂`, `|τ| ≤ τ₀` and `x₁ ≤ Re w ≤ x₂`,
`|K_s(w)| (1 + |Im w|)^n ≤ C`. From `norm_Gamma_mul_one_add_abs_im_pow_le` for `Γ(w)`, the bound
`|Γ(s - w)| ≤ Γ(Re(s - w))` on `Re(s - w) ∈ [σ₁ - x₂, σ₂ - x₁] ⊂ (0, ∞)`, and boundedness of `1/Γ` on the compact
rectangle. -/
theorem norm_KerS_mul_pow_le {x₁ x₂ σ₁ σ₂ τ₀ : ℝ} (hx₁ : 0 < x₁) (hx : x₂ < σ₁) (n : ℕ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |s.im| ≤ τ₀ → ∀ w : ℂ, x₁ ≤ w.re → w.re ≤ x₂ →
      ‖KerS s w‖ * (1 + |w.im|) ^ n ≤ C := by
  by_cases hne : x₁ ≤ x₂
  swap
  · exact ⟨0, fun s _ _ _ w h1 h2 => absurd (h1.trans h2) hne⟩
  obtain ⟨C1, hC1⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := x₁) (a' := x₂) hx₁ n
  obtain ⟨C2, hC2⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le
    (a := σ₁ - x₂) (a' := σ₂ - x₁) (by linarith) 0
  have hK : IsCompact (Icc σ₁ σ₂ ×ℂ Icc (-τ₀) τ₀) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun s : ℂ => (Gamma s)⁻¹) (Icc σ₁ σ₂ ×ℂ Icc (-τ₀) τ₀) := by
    have := Complex.differentiable_one_div_Gamma.continuous
    exact (this.continuousOn).congr fun s _ => by simp
  obtain ⟨C3, hC3⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨C1 * C2 * C3, fun s hs1 hs2 hsi w hw1 hw2 => ?_⟩
  have hs : s ∈ Icc σ₁ σ₂ ×ℂ Icc (-τ₀) τ₀ :=
    ⟨⟨hs1, hs2⟩, ⟨(abs_le.mp hsi).1, (abs_le.mp hsi).2⟩⟩
  have h1 := hC1 w hw1 hw2
  have h2 := hC2 (s - w) (by simp; linarith) (by simp; linarith)
  simp only [pow_zero, mul_one] at h2
  have h3 := hC3 s hs
  have hC1n : 0 ≤ C1 := le_trans (by positivity) h1
  have hC2n : 0 ≤ C2 := le_trans (norm_nonneg _) h2
  rw [KerS, div_eq_mul_inv, norm_mul, norm_mul]
  calc ‖Gamma w‖ * ‖Gamma (s - w)‖ * ‖(Gamma s)⁻¹‖ * (1 + |w.im|) ^ n
      = (‖Gamma w‖ * (1 + |w.im|) ^ n) * ‖Gamma (s - w)‖ * ‖(Gamma s)⁻¹‖ := by ring
    _ ≤ C1 * C2 * C3 := by gcongr

end GoldbachBoundaries.Paper2.M1
