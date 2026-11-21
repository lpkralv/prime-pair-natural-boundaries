import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.J_spec

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

/-- **Values of `X'_α(α)`** (the local model, "Values"; the kernel lemma (3),(4); the pole-set lemma for `Q`(ii)).

Sketch. `deriv (X α) α` by `J_spec` and `Kern (1 + a) 1 = Γ(1)Γ(a)/Γ(1+a) = 1/a`
(`Complex.Gamma_add_one`, `Γ(a) ≠ 0` for `Re a > 0`); `Kern 2 1 = 1`. Then `sigmaRes` values:
`sigmaRes_eq` with `hasResidue_Qcont_inv` (`μ(k)/k`) and `hasResidue_Qcont_zero hRH`
(`-μ(n)m(ρ)/n`), `SigmaMeromorphic.lean`: `2·(μ(k)/k)·k = 2μ(k)`,
`2·(-μ(n)m(ρ)/n)·(n/ρ) = -2μ(n)m(ρ)/ρ`. For `α = 1 + 1/k`, `α ≠ 2`; for `α = 1 + ρ/n`, `α ≠ 2`
(real parts). Non-vanishing: `μ(n) ≠ 0` for squarefree `n` (`mu_ne_zero_of_squarefree`),
`m(ρ) ≥ 1` (`one_le_zetaMult_of_zero`), `ρ ≠ 0`. For the third clause of `HasCatalogueValues` the
point `1 + ρ/n` determines `(n, ρ)` only under RH; no uniqueness is needed here since `deriv (X α) α`
is computed from `α` itself. -/
theorem X_deriv_spec (hRH : RiemannHypothesis) :
    HasCatalogueValues (fun α => deriv (X α) α) ∧ ∀ α ∈ catalogue, deriv (X α) α ≠ 0 := by
  have hG2 : Gamma (2 : ℂ) = 1 := by
    simpa using Gamma_add_one 1 one_ne_zero
  have htwo : deriv (X 2) 2 = 1 := by
    have h := (J_spec (a := 1) (b := 1) (by norm_num) (by norm_num)).2.deriv
    have he : X 2 = J 1 1 := by funext s; simp [X]
    rw [he]
    convert h using 1 <;> norm_num [Kern, hG2]
  have hd : ∀ a : ℂ, 0 < a.re → a ≠ 1 →
      deriv (X (1 + a)) (1 + a) = 2 * sigmaRes a / a := by
    intro a ha ha1
    have ha0 : a ≠ 0 := by intro he; simpa [he] using ha
    have h2 : (1 : ℂ) + a ≠ 2 := by intro he; apply ha1; linear_combination he
    have he : X (1 + a) = fun s => (2 * sigmaRes a) * J 1 a s := by
      funext s
      simp [X, h2]
    have hK : Kern (1 + a) 1 = 1 / a := by
      simp only [Kern, Gamma_one, one_mul, add_sub_cancel_left]
      rw [add_comm, Gamma_add_one a ha0]
      field_simp [Gamma_ne_zero_of_re_pos ha]
    rw [he]
    have h := ((J_spec (a := 1) (b := a) (by norm_num) ha).2.const_mul (2 * sigmaRes a)).deriv
    simpa [hK, div_eq_mul_inv] using h
  have hk1 : ∀ k : ℕ, 2 ≤ k → 1 / (k : ℂ) ≠ 1 := by
    intro k hk he
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [div_eq_one_iff_eq hk0] at he
    have : k = 1 := by exact_mod_cast he.symm
    omega
  have hρ1 : ∀ n : ℕ, 1 ≤ n → ∀ ρ ∈ NontrivialZeros, ρ / (n : ℂ) ≠ 1 := by
    intro n hn ρ hρ he
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [div_eq_one_iff_eq hn0] at he
    have hre := congrArg Complex.re he
    simp only [natCast_re] at hre
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [hρ.2.2]
  constructor
  · refine ⟨htwo, ?_, ?_⟩
    · intro k hk hsq
      dsimp only
      rw [hd _ (one_div_natCast_re_pos (by omega)) (hk1 k hk),
        sigmaRes_eq (hasResidue_Qcont_inv hk)]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp
    · intro n hn hsq ρ hρ
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hr0 : ρ ≠ 0 := by intro he; simpa [he] using hρ.2.1
      have hp : 0 < (ρ / (n : ℂ)).re := by
        rw [Complex.div_natCast_re]
        exact div_pos hρ.2.1 (by exact_mod_cast (by omega : 0 < n))
      dsimp only
      rw [hd _ hp (hρ1 n hn ρ hρ), sigmaRes_eq (hasResidue_Qcont_zero hRH hn hρ)]
      field_simp
  · intro α hα
    by_cases h2 : α = 2
    · simpa [h2, htwo]
    · have ha := sub_one_mem_poleSetQ_of_mem_catalogue hα
      have hp := re_pos_of_mem_poleSetQ ha
      have ha1 : α - 1 ≠ 1 := by intro he; apply h2; linear_combination he
      have he : 1 + (α - 1) = α := by ring
      have hv := hd _ hp ha1
      rw [he] at hv
      rw [hv]
      obtain ⟨c, hc, hr⟩ := exists_hasResidue_Qcont_ne_zero hRH ha
      rw [sigmaRes_eq hr]
      exact div_ne_zero (mul_ne_zero (by norm_num) hc)
        (by intro he; simpa [he] using hp)

end GoldbachBoundaries.ThmA
