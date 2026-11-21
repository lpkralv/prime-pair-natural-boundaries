import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.pinchPairs_finite

/-!
# `finsum_nu_eq_pairSum`

One bookkeeping identity replaces a three-case argument. Write `g(x) = R_x R_{s₀-x} B(x, s₀-x)` and
`f(a, b) = R_a R_b B(a, b)` (so `f(a, b) = f(b, a)`), and `ν(x) = [Re x > c] + [Re(s₀ - x) < c]`. Then

* the pairs `(a, b)` with `Re a > c` are exactly `(x, s₀ - x)` for `x ∈ S = {x ∈ F_δ : s₀ - x ∈ Σ_Q}`, `Re x > c`
  (`Re a > c > B_∞ + δ` puts `a` in `F_δ`);
* the pairs `(a, b)` with `Re a ≤ c` are exactly `(s₀ - x, x)` for `x ∈ S`, `Re(s₀ - x) < c` (then
  `Re b ≥ Re s₀ - c > B_∞ + 2δ` puts `b` in `F_δ`; and `Re a ≠ c`: if `a ∈ F_δ` by admissibility, otherwise
  `Re a ≤ B_∞ + δ < c`).

So `∑_{x ∈ S} ν(x) g(x) = ∑_{Re a > c} f + ∑_{Re a ≤ c} f = 𝓡(s₀)`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The indicator sum is the pair sum** (Z1; the paper's three cases). For admissible `(δ, c)` and `s₀` in the region
(so `Re s₀ > 2B_∞ + 4δ`): each ordered pair `(a, b)`, `a + b = s₀`, has a member in `F_δ`; for `a ≠ b` both in `F_δ`,
`ν(a) + ν(b) = 2`; for `a ∈ F_δ`, `b ∉ F_δ`, `ν(a) = 2`; for `a = b`, `ν(a) = 1`; `B(a, b) = B(b, a)`. `pairSum` is a
`tsum` over the finite set `pinchPairs s₀`. Uses: `pinchPairs_finite`, `Fdelta_spec`. -/
theorem finsum_nu_eq_pairSum (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) {s₀ : ℂ} (hs₀ : s₀ ∈ RegC δ c) :
    ∑ᶠ x ∈ {x | x ∈ Fdelta δ ∧ s₀ - x ∈ PoleSetQ},
      nu c x s₀ * Rcoef x * Rcoef (s₀ - x) * betaB x (s₀ - x) = pairSum s₀ := by
  classical
  obtain ⟨hδ, -, hc1, -, hcne⟩ := h
  have hreg : c + Binf + 2 * δ < s₀.re := hs₀.1
  have hF := (Fdelta_spec hZ1 δ hδ).1
  set S : Set ℂ := {x | x ∈ Fdelta δ ∧ s₀ - x ∈ PoleSetQ} with hSdef
  have hS : S.Finite := hF.subset fun x hx => hx.1
  have hP : (pinchPairs s₀).Finite := pinchPairs_finite hZ1 (by linarith)
  set g : ℂ → ℂ := fun x => Rcoef x * Rcoef (s₀ - x) * betaB x (s₀ - x) with hgdef
  set f : ℂ × ℂ → ℂ := fun p => Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2 with hfdef
  -- the left side as two filtered finite sums
  have hL : ∑ᶠ x ∈ S, nu c x s₀ * Rcoef x * Rcoef (s₀ - x) * betaB x (s₀ - x) =
      ∑ x ∈ hS.toFinset.filter (fun x => c < x.re), g x +
        ∑ x ∈ hS.toFinset.filter (fun x => s₀.re - x.re < c), g x := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [nu, iverson, hgdef]
    split_ifs <;> ring
  -- the right side as two filtered finite sums
  have hR : pairSum s₀ =
      ∑ p ∈ hP.toFinset.filter (fun p => c < p.1.re), f p +
        ∑ p ∈ hP.toFinset.filter (fun p => ¬ c < p.1.re), f p := by
    rw [Finset.sum_filter_add_sum_filter_not, pairSum, ← Finset.tsum_subtype' hP.toFinset f,
      hP.coe_toFinset]
  rw [hL, hR]
  congr 1
  · -- pairs with `Re a > c`
    refine Finset.sum_nbij' (fun x => (x, s₀ - x)) (fun p => p.1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hx ⊢
      exact ⟨⟨hx.1.1.1, hx.1.2, by ring⟩, hx.2⟩
    · intro p hp
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hp ⊢
      obtain ⟨⟨h1, h2, h12⟩, hpc⟩ := hp
      refine ⟨⟨⟨h1, by linarith⟩, ?_⟩, hpc⟩
      rw [← h12]; simpa using h2
    · intro x _; rfl
    · intro p hp
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
      obtain ⟨⟨-, -, h12⟩, -⟩ := hp
      ext <;> simp [← h12]
    · intro x _; rfl
  · -- pairs with `Re a ≤ c`
    refine Finset.sum_nbij' (fun x => (s₀ - x, x)) (fun p => p.2) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hx ⊢
      refine ⟨⟨hx.1.2, hx.1.1.1, by ring⟩, ?_⟩
      simp only [sub_re]
      linarith [hx.2]
    · intro p hp
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hp ⊢
      obtain ⟨⟨h1, h2, h12⟩, hpc⟩ := hp
      push Not at hpc
      have hre : p.1.re + p.2.re = s₀.re := by rw [← h12]; simp
      have hne : p.1.re ≠ c := by
        intro he
        by_cases hpF : Binf + δ < p.1.re
        · exact hcne p.1 ⟨h1, hpF⟩ he.symm
        · linarith
      refine ⟨⟨⟨h2, by linarith⟩, ?_⟩, ?_⟩
      · rw [← h12]; simpa using h1
      · have : p.1.re < c := lt_of_le_of_ne hpc hne
        linarith
    · intro x _; rfl
    · intro p hp
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
      obtain ⟨⟨-, -, h12⟩, -⟩ := hp
      ext <;> simp [← h12]
    · intro x _
      simp only [hgdef, hfdef, betaB, sub_add_cancel, add_sub_cancel]
      ring

end GoldbachBoundaries.Paper2.M1
