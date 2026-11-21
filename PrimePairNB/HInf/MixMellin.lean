import PrimePairNB.HInf.MixDefs
import PrimePairNB.Paper2.M4b.Fill.ACommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M4b
namespace GoldbachBoundaries.HInf.MixProof

private def Aterm (ω : ℕ → ℝ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  (ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-w)

/-- Mellin–Barnes interchange with independently chosen prime weights. -/
theorem tsum_eq_verticalIntegral'_two_weights {ω₁ ω₂ : ℕ → ℝ} (hω₁ : PrimeWeight ω₁) (hω₂ : PrimeWeight ω₂) {L : ℂ} {c : ℝ}
    (hc1 : 1 < c) (hc2 : c < L.re - 1) {f : ℝ → ℂ} {k : ℂ → ℂ}
    (hk : Integrable (fun y : ℝ => k (c + y * I)))
    (hf : ∀ t : ℝ, 0 < t → f t = VerticalIntegral' (fun z => k z * (t : ℂ) ^ (-z)) c) :
    Summable (fun pq : Nat.Primes × Nat.Primes =>
      ‖(ω₁ (pq.1 : ℕ) : ℂ) * (ω₂ (pq.2 : ℕ) : ℂ) * ((pq.2 : ℕ) : ℂ) ^ (-L) *
        f (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ))‖) ∧
    Integrable (fun y : ℝ => k (c + y * I) * primeSum ω₁ (c + y * I) * primeSum ω₂ (L - (c + y * I))) ∧
    ∑' pq : Nat.Primes × Nat.Primes,
        (ω₁ (pq.1 : ℕ) : ℂ) * (ω₂ (pq.2 : ℕ) : ℂ) * ((pq.2 : ℕ) : ℂ) ^ (-L) * f (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ)) =
      VerticalIntegral' (fun z => k z * primeSum ω₁ z * primeSum ω₂ (L - z)) c := by
  have hc0 : 0 < c := by linarith
  have hcs : c < L.re := by linarith
  have hre1 : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  have hre2 : ∀ y : ℝ, (L - ((c : ℂ) + y * I)).re = L.re - c := fun y => by simp
  -- the `(p, q)` integrand on the line
  set F : Nat.Primes × Nat.Primes → ℝ → ℂ := fun pq y =>
    k (c + y * I) * (Aterm ω₁ pq.1 (c + y * I) * Aterm ω₂ pq.2 (L - (c + y * I))) with hF
  -- Step A: rewriting `F` through the one-pair Mellin–Barnes integrand
  have hFeq : ∀ pq : Nat.Primes × Nat.Primes, ∀ y : ℝ,
      F pq y = ((ω₁ (pq.1 : ℕ) : ℂ) * (ω₂ (pq.2 : ℕ) : ℂ) *
        ((pq.2 : ℕ) : ℂ) ^ (-L)) *
        (k (c + y * I) *
          ((((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I))) := by
    intro pq y
    have hq0 : ((pq.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pq.2.prop.ne_zero
    rw [A_div_cpow_primes, hF]
    simp only [Aterm]
    have hsplit : ((pq.2 : ℕ) : ℂ) ^ (-(L - ((c : ℂ) + y * I))) =
        ((pq.2 : ℕ) : ℂ) ^ (-L) * ((pq.2 : ℕ) : ℂ) ^ ((c : ℂ) + y * I) := by
      rw [← cpow_add _ _ hq0]; congr 1; ring
    rw [hsplit]
    ring
  have htpos : ∀ pq : Nat.Primes × Nat.Primes, 0 < ((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) :=
    fun pq => div_pos (by exact_mod_cast pq.1.prop.pos) (by exact_mod_cast pq.2.prop.pos)
  -- Step C: summability of the `L¹` norms
  set a : Nat.Primes → ℝ := fun p => ‖Aterm ω₁ p (c : ℂ)‖ with ha
  set b : Nat.Primes → ℝ := fun q => ‖Aterm ω₂ q ((L.re - c : ℝ) : ℂ)‖ with hb
  have hasum : Summable a := by
    have := hω₁.2 (z := (c : ℂ)) (by simpa using hc1)
    exact this
  have hbsum : Summable b := by
    have := hω₂.2 (z := ((L.re - c : ℝ) : ℂ)) (by simp; linarith)
    exact this
  have hnormF : ∀ pq : Nat.Primes × Nat.Primes, ∀ y : ℝ,
      ‖F pq y‖ = ‖k (c + y * I)‖ * (a pq.1 * b pq.2) := by
    intro pq y
    rw [hF]
    dsimp only
    rw [norm_mul, norm_mul]
    simp only [ha, hb, Aterm]
    rw [A_norm_term_re ω₁ pq.1 ((c : ℂ) + y * I), A_norm_term_re ω₂ pq.2 (L - ((c : ℂ) + y * I)),
      hre1, hre2]
  have hab : Summable fun pq : Nat.Primes × Nat.Primes => a pq.1 * b pq.2 :=
    hasum.mul_of_nonneg hbsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hFint : ∀ pq : Nat.Primes × Nat.Primes, Integrable (F pq) := by
    intro pq
    apply Integrable.mono' (hk.norm.mul_const (a pq.1 * b pq.2))
    · apply hk.aestronglyMeasurable.mul
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · exact continuous_const.mul (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast pq.1.prop.ne_zero)))
      · exact continuous_const.mul (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast pq.2.prop.ne_zero)))
    · exact Eventually.of_forall fun y => (hnormF pq y).le
  have hsumF : Summable fun pq : Nat.Primes × Nat.Primes => ∫ y : ℝ, ‖F pq y‖ := by
    refine (hab.mul_left (∫ y : ℝ, ‖k (c + y * I)‖)).congr fun pq => ?_
    simp_rw [hnormF pq]
    rw [integral_mul_const]
  have hterm : ∀ pq : Nat.Primes × Nat.Primes,
      (ω₁ (pq.1 : ℕ) : ℂ) * (ω₂ (pq.2 : ℕ) : ℂ) *
        ((pq.2 : ℕ) : ℂ) ^ (-L) *
        f (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ)) =
      (1 / (2 * Real.pi * I)) * (I * ∫ y : ℝ, F pq y) := by
    intro pq
    rw [hf _ (htpos pq), VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul]
    simp_rw [hFeq pq]
    rw [integral_const_mul]
    ring
  -- Step D: the interchange, and the inner sum
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumF
  have hinner : ∀ y : ℝ, ∑' pq : Nat.Primes × Nat.Primes, F pq y =
      k (c + y * I) * primeSum ω₁ (c + y * I) * primeSum ω₂ (L - (c + y * I)) := by
    intro y
    rw [hF]
    simp only
    rw [tsum_mul_left, mul_assoc]
    congr 1
    rw [primeSum, primeSum]
    refine (tsum_mul_tsum_of_summable_norm (f := fun p => Aterm ω₁ p (c + y * I))
      (g := fun q => Aterm ω₂ q (L - (c + y * I))) ?_ ?_).symm
    · exact hω₁.2 _ (by rw [hre1]; exact hc1)
    · exact hω₂.2 _ (by rw [hre2]; linarith)
  have hpoint : ∀ y : ℝ, Summable (fun pq : Nat.Primes × Nat.Primes => ‖F pq y‖) := by
    intro y
    exact (hab.mul_left ‖k (c + y * I)‖).congr fun pq => (hnormF pq y).symm
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ∑' pq, F pq y) :=
    AEStronglyMeasurable.tsum (fun pq => (hFint pq).aestronglyMeasurable)
  have hint : Integrable (fun y : ℝ => ∑' pq, F pq y) := by
    refine Integrable.mono' (hk.norm.mul_const (∑' pq : Nat.Primes × Nat.Primes, a pq.1 * b pq.2)) hmeas ?_
    apply Eventually.of_forall
    intro y
    calc ‖∑' pq, F pq y‖ ≤ ∑' pq, ‖F pq y‖ := norm_tsum_le_tsum_norm (hpoint y)
      _ = ‖k (c + y * I)‖ * ∑' pq : Nat.Primes × Nat.Primes, a pq.1 * b pq.2 := by
        simp_rw [hnormF]
        rw [tsum_mul_left]
  refine ⟨?_, ?_, ?_⟩
  · have hnormI : Summable (fun pq => ‖∫ y : ℝ, F pq y‖) :=
      hsumF.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
    simp_rw [hterm]
    simpa only [norm_mul, mul_assoc] using
      (hnormI.mul_left (‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖I‖))
  · simpa only [hinner] using hint
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left, hswap]
    simp_rw [hinner]
    rfl

end GoldbachBoundaries.HInf.MixProof
