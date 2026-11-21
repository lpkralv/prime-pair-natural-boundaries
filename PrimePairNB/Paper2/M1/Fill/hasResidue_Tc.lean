import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.Ic_differentiableOn
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.hasResidue_Qcont_Rcoef
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

/-!
# `hasResidue_Tc`

`𝒯_c = I_c + ∑_{a ∈ F_δ} ν(a, s) R_a K_s(a) Q(s - a)`, a finite sum (`Fdelta_spec`). At `s₀` in the region:

* `I_c` is holomorphic at `s₀` (`Ic_differentiableOn`, `isOpen_RegC`): residue `0`;
* `ν(a, ·)` is constant near `s₀`, since `Re s₀ ≠ c + Re a`;
* `s ↦ R_a K_s(a)` is continuous at `s₀` (`Re s₀ > 1 ≥ Re a`, so `Γ` is regular at `s₀ - a` and `s₀`, `Γ(s₀) ≠ 0`);
* `s ↦ Q(s - a)` has residue `R_{s₀ - a}` at `s₀` when `s₀ - a ∈ Σ_Q` (`hasResidue_Qcont_Rcoef`,
  `HasResidue.comp_sub_const`), and is continuous at `s₀` otherwise (`analyticAt_Qcont_sub_sum`,
  `regular_of_not_mem_poleSetQ`).

The residue of a term is then `ν(a, s₀) R_a K_{s₀}(a) R_{s₀ - a}` or `0`, and `K_{s₀}(a) = B(a, s₀ - a)`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Multiplying by a function continuous at the point multiplies the residue by its value. -/
theorem HasResidue.mul_continuousAt_D {f φ : ℂ → ℂ} {a c : ℂ} (hf : HasResidue f a c)
    (hφ : ContinuousAt φ a) : HasResidue (fun z => φ z * f z) a (φ a * c) := by
  unfold HasResidue at hf ⊢
  refine ((hφ.tendsto.mono_left nhdsWithin_le_nhds).mul hf).congr fun z => ?_
  ring

/-- The residue of a finite sum is the sum of the residues. -/
theorem HasResidue.finset_sum_D {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {a : ℂ} {c : ι → ℂ}
    (hf : ∀ i ∈ s, HasResidue (f i) a (c i)) :
    HasResidue (fun z => ∑ i ∈ s, f i z) a (∑ i ∈ s, c i) := by
  unfold HasResidue at hf ⊢
  simp_rw [Finset.mul_sum]
  exact tendsto_finsetSum _ hf

/-- `Γ` is continuous at points of positive real part. -/
theorem continuousAt_Gamma_of_re_pos_D {z : ℂ} (hz : 0 < z.re) : ContinuousAt Gamma z := by
  refine (Complex.differentiableAt_Gamma z fun m hm => ?_).continuousAt
  rw [hm] at hz
  simp only [neg_re, natCast_re] at hz
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **Residue of `𝒯_c`** (Z1, Z2, Z3) at a point `s₀` of the region: `I_c` is holomorphic there, the indicators are
constant near `s₀`, and the term of index `x ∈ F_δ` has residue `ν(x) R_x R_{s₀-x} K_{s₀}(x)` when `s₀ - x ∈ Σ_Q`
(`hasResidue_Qcont_Rcoef` and `HasResidue.comp_sub_const`; `K_{s₀}(x) = B(x, s₀ - x)`), and is holomorphic otherwise.
Uses: `Ic_differentiableOn`, `isOpen_RegC`, `hasResidue_Qcont_Rcoef`, `meromorphicOrderAt_Qcont_ge`,
`analyticAt_Qcont_sub_sum`, `regular_of_not_mem_poleSetQ`, `Fdelta_spec`. -/
theorem hasResidue_Tc (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) {s₀ : ℂ}
    (hs₀ : s₀ ∈ RegC δ c) :
    HasResidue (Tc δ c) s₀ (∑ᶠ x ∈ {x | x ∈ Fdelta δ ∧ s₀ - x ∈ PoleSetQ},
      nu c x s₀ * Rcoef x * Rcoef (s₀ - x) * betaB x (s₀ - x)) := by
  classical
  have hδ : 0 < δ := h.1
  have hc1 : Binf + 2 * δ < c := h.2.2.1
  have hreg : c + Binf + 2 * δ < s₀.re := hs₀.1
  have hregne : ∀ a ∈ Fdelta δ, s₀.re ≠ c + a.re := hs₀.2
  have hB : 1 / 2 ≤ Binf := half_le_Binf hZ1
  have hs₀1 : 1 < s₀.re := by linarith
  have hF := (Fdelta_spec hZ1 δ hδ).1
  set FT := hF.toFinset with hFTdef
  -- the residue of each term
  set r : ℂ → ℂ := fun a => if s₀ - a ∈ PoleSetQ then
    nu c a s₀ * Rcoef a * Rcoef (s₀ - a) * betaB a (s₀ - a) else 0 with hrdef
  have hterm : ∀ a ∈ FT, HasResidue (fun s => nu c a s * Rcoef a * KerS s a * Qcont (s - a)) s₀ (r a) := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    have haS : a ∈ PoleSetQ := ha.1
    have ha1 : a.re ≤ 1 := (poleSetQ_re_bounds haS).2.1
    have hsa : 0 < (s₀ - a).re := by simp only [sub_re]; linarith
    have hs0 : 0 < s₀.re := by linarith
    -- `ν` is locally constant
    have hnu : ∀ᶠ s in 𝓝 s₀, nu c a s = nu c a s₀ := by
      have hne : s₀.re - a.re ≠ c := fun he => hregne a ha (by linarith)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [(continuous_re.tendsto s₀).eventually (gt_mem_nhds (show s₀.re < c + a.re by
          linarith))] with s hs
        have h1 : s.re - a.re < c := by linarith
        simp [nu, iverson, h1, hlt]
      · filter_upwards [(continuous_re.tendsto s₀).eventually (lt_mem_nhds (show c + a.re < s₀.re by
          linarith))] with s hs
        have h1 : ¬ s.re - a.re < c := by linarith
        have h2 : ¬ s₀.re - a.re < c := by linarith
        simp [nu, iverson, h1, h2]
    -- the continuous factor
    set φ : ℂ → ℂ := fun s => nu c a s₀ * Rcoef a * KerS s a with hφdef
    have hφ : ContinuousAt φ s₀ := by
      have hG1 : ContinuousAt (fun s => Gamma (s - a)) s₀ :=
        (continuousAt_Gamma_of_re_pos_D hsa).comp (f := fun s => s - a)
          (continuousAt_id.sub continuousAt_const)
      have hG2 : ContinuousAt Gamma s₀ := continuousAt_Gamma_of_re_pos_D hs0
      have hG0 : Gamma s₀ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
      simp only [hφdef, KerS]
      exact continuousAt_const.mul ((continuousAt_const.mul hG1).div hG2 hG0)
    have heq : (fun s => nu c a s * Rcoef a * KerS s a * Qcont (s - a)) =ᶠ[𝓝[≠] s₀]
        fun s => φ s * Qcont (s - a) := by
      filter_upwards [nhdsWithin_le_nhds hnu] with s hs
      simp only [hφdef, hs]
    refine HasResidue.congr ?_ heq.symm
    by_cases hP : s₀ - a ∈ PoleSetQ
    · have hQ : HasResidue (fun s => Qcont (s - a)) s₀ (Rcoef (s₀ - a)) := by
        simpa using (hasResidue_Qcont_Rcoef hP).comp_sub_const a
      have := HasResidue.mul_continuousAt_D hQ hφ
      convert this using 1
      simp only [hrdef, hP, ite_true, hφdef, KerS, betaB, add_sub_cancel]
      ring
    · have hQa : AnalyticAt ℂ Qcont (s₀ - a) := by
        have := analyticAt_Qcont_sub_sum hsa ∅
          (fun n _ hmu => regular_of_not_mem_poleSetQ hsa hP hmu)
        simpa using this
      have hcont : ContinuousAt (fun s => φ s * Qcont (s - a)) s₀ :=
        hφ.mul (hQa.continuousAt.comp (f := fun s => s - a) (continuousAt_id.sub continuousAt_const))
      simpa [hrdef, hP] using hasResidue_zero_of_continuousAt hcont
  -- `I_c` is holomorphic at `s₀`
  have hIc : AnalyticAt ℂ (IcQ Qcont c) s₀ :=
    (Ic_differentiableOn hZ1 hZ2 hZ3 h).analyticAt ((isOpen_RegC hZ1 h).mem_nhds hs₀)
  have hsum := (HasResidue.finset_sum_D FT hterm).add_analyticAt hIc
  have hfun : (fun s => ∑ a ∈ FT, nu c a s * Rcoef a * KerS s a * Qcont (s - a) + IcQ Qcont c s) =
      Tc δ c := by
    funext s
    rw [Tc, TcQ, finsum_mem_eq_finite_toFinset_sum _ hF, add_comm]
  rw [hfun] at hsum
  convert hsum using 1
  have hS : {x | x ∈ Fdelta δ ∧ s₀ - x ∈ PoleSetQ}.Finite := hF.subset fun x hx => hx.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, hrdef, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [hFTdef]

end GoldbachBoundaries.Paper2.M1
