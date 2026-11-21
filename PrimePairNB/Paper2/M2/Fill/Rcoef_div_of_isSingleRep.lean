import PrimePairNB.Paper2.M2.Rigidity

/-! `Rcoef_div_of_isSingleRep` of `Paper2/M2/Single.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`R_u = m(ρ)/q` for a single representation** (unconditional). `u = ρ/q ∈ Σ_Q` (`n = q`, primes are
squarefree), `Im u ≠ 0`, so `Rcoef_eq_finsum` applies; its index set is `{q}`: every index `k` gives the
representation `(ku, k)` of `u`, so `k = q` by `IsSingleRep`; and `q` is an index (`q < 1/Re u = q/β` as `β < 1`,
`qu = ρ` a zero). With `μ(q) = -1` (`ArithmeticFunction.moebius_apply_prime`): `R_u = m(ρ)/q`. Then
`2R_u/u = 2m(ρ)/ρ` and its norm is `2m(ρ)/|ρ|`. -/
theorem Rcoef_div_of_isSingleRep {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) {q : ℕ} (hq : q.Prime)
    (hs : IsSingleRep ρ q) :
    Rcoef (ρ / (q : ℂ)) = (zetaMult ρ : ℂ) / q ∧
      ‖2 * Rcoef (ρ / (q : ℂ)) / (ρ / (q : ℂ))‖ = 2 * zetaMult ρ / ‖ρ‖ := by
  have hn : 1 ≤ q := hq.one_lt.le
  have hsq : Squarefree q := hq.squarefree
  have hn0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hρ0 : ρ ≠ 0 := ne_zero_of_mem_nontrivialZeros hρ
  have hnR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hu : ρ / (q : ℂ) ∈ PoleSetQ := Or.inr ⟨q, hn, hsq, ρ, hρ, rfl⟩
  have hre : (ρ / (q : ℂ)).re = ρ.re / q := by simp
  have him : (ρ / (q : ℂ)).im ≠ 0 := by
    have : (ρ / (q : ℂ)).im = ρ.im / q := by simp
    rw [this]; exact div_ne_zero (im_ne_zero_of_mem_nontrivialZeros hρ) hnR.ne'
  have hset : {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / (ρ / (q : ℂ)).re ∧
      (k : ℂ) * (ρ / (q : ℂ)) ∈ NontrivialZeros} = {q} := by
    ext k
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hk1, hksq, -, hkz⟩
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      exact (hs _ k ⟨hkz, hk1, hksq, by field_simp⟩).2
    · rintro rfl
      refine ⟨hn, hsq, ?_, ?_⟩
      · rw [hre, one_div_div, lt_div_iff₀ hρ.2.1]
        nlinarith [hρ.2.2]
      · rwa [mul_div_cancel₀ _ hn0]
  have hR := Rcoef_eq_finsum hu him
  rw [hset, finsum_mem_singleton, mul_div_cancel₀ _ hn0] at hR
  have hmu : mu q = -1 := by
    simp [mu, ArithmeticFunction.moebius_apply_prime hq]
  have hR' : Rcoef (ρ / (q : ℂ)) = (zetaMult ρ : ℂ) / q := by
    rw [hR, hmu]; ring
  refine ⟨hR', ?_⟩
  rw [hR']
  have : 2 * ((zetaMult ρ : ℂ) / q) / (ρ / (q : ℂ)) = 2 * (zetaMult ρ : ℂ) / ρ := by
    field_simp
  rw [this, norm_div, norm_mul, Complex.norm_natCast]
  norm_num

end GoldbachBoundaries.Paper2.M2
