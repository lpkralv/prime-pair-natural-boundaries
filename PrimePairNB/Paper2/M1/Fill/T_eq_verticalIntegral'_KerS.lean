import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'

/-!
# `T_eq_verticalIntegral'_KerS`: the Mellin–Barnes representation of `T` without (Z6)

For each ordered pair `(p, q)`, `one_add_cpow_neg_eq_verticalIntegral'` at `t = p/q` gives
`log p log q (p+q)^{-s} = (2πi)⁻¹ ∫_{(c)} K_s(w) (log p p^{-w}) (log q q^{-(s-w)}) dw`.
Sum over pairs and interchange (`integral_tsum_of_summable_integral_norm`): the `L¹` norm of the
`(p, q)` integrand is `‖K_s‖_{L¹(c)} · log p p^{-c} · log q q^{c-σ}`, summable over pairs. The inner sum
is `K_s(w) Q(w) Q(s-w)` (`tsum_mul_tsum_of_summable_norm`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The term `log p · p^{-w}` of `Q`. -/
private def qt (p : Nat.Primes) (w : ℂ) : ℂ := (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-w)

/-- `(p/q)^{-w} = p^{-w} q^{w}` for primes `p, q`. -/
private lemma div_cpow_primes (p q : Nat.Primes) (w : ℂ) :
    ((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (-w) =
      ((p : ℕ) : ℂ) ^ (-w) * ((q : ℕ) : ℂ) ^ w := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have harg : (((q : ℕ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hp (inv_nonneg.mpr hq.le), ofReal_inv,
    inv_cpow _ _ harg, ← cpow_neg, neg_neg, ofReal_natCast, ofReal_natCast]

/-- `(p + q)^{-s} = q^{-s} (1 + p/q)^{-s}`. -/
private lemma add_cpow_primes (p q : Nat.Primes) (s : ℂ) :
    ((((p : ℕ) + (q : ℕ) : ℕ) : ℂ)) ^ (-s) =
      ((q : ℕ) : ℂ) ^ (-s) * ((1 + ((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (-s) := by
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have h1 : (0 : ℝ) ≤ 1 + ((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) := by positivity
  have hq' : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have he : ((((p : ℕ) + (q : ℕ) : ℕ) : ℂ)) =
      ((((q : ℕ) : ℝ) * (1 + ((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, ofReal_mul, mul_cpow_ofReal_nonneg hq.le h1, ofReal_natCast]

/-- **Mellin–Barnes representation of `T` without (Z6)**: `T(s) = (1/2πi) ∫_{(c)} K_s(w) Q(w) Q(s-w) dw` for `σ > 2`, `1 < c < σ - 1`. Put
`t = p/q` in `one_add_cpow_neg_eq_verticalIntegral'` (`(p+q)^{-s} = q^{-s}(1 + p/q)^{-s}`), multiply by
`log p log q`, sum over `(p, q)` and interchange sum and integral (Fubini–Tonelli: `∑ log p p^{-c} = Q(c)`,
`∑ log q q^{c-σ} = Q(σ - c)` converge absolutely, and `∫ |K_s(c+it)| dt < ∞`). Uses:
`one_add_cpow_neg_eq_verticalIntegral'`, `norm_KerS_mul_pow_le`. -/
theorem T_eq_verticalIntegral'_KerS {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc1 : 1 < c)
    (hc2 : c < s.re - 1) :
    T s = VerticalIntegral' (fun w => KerS s w * Q w * Q (s - w)) c := by
  have hc0 : 0 < c := by linarith
  have hcs : c < s.re := by linarith
  have hre1 : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  have hre2 : ∀ y : ℝ, (s - ((c : ℂ) + y * I)).re = s.re - c := fun y => by simp
  -- the `(p, q)` integrand on the line
  set F : Nat.Primes × Nat.Primes → ℝ → ℂ := fun pq y =>
    KerS s (c + y * I) * (qt pq.1 (c + y * I) * qt pq.2 (s - (c + y * I))) with hF
  -- Step A: rewriting `F` through the one-pair Mellin–Barnes integrand
  have hFeq : ∀ pq : Nat.Primes × Nat.Primes, ∀ y : ℝ,
      F pq y = ((Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) *
        ((pq.2 : ℕ) : ℂ) ^ (-s)) *
        (KerS s (c + y * I) *
          ((((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I))) := by
    intro pq y
    have hq0 : ((pq.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pq.2.prop.ne_zero
    rw [div_cpow_primes, hF]
    simp only [qt]
    have hsplit : ((pq.2 : ℕ) : ℂ) ^ (-(s - ((c : ℂ) + y * I))) =
        ((pq.2 : ℕ) : ℂ) ^ (-s) * ((pq.2 : ℕ) : ℂ) ^ ((c : ℂ) + y * I) := by
      rw [← cpow_add _ _ hq0]; congr 1; ring
    rw [hsplit]
    ring
  have htpos : ∀ pq : Nat.Primes × Nat.Primes, 0 < ((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) :=
    fun pq => div_pos (by exact_mod_cast pq.1.prop.pos) (by exact_mod_cast pq.2.prop.pos)
  -- Step B: each `F pq` is integrable
  have hFint : ∀ pq : Nat.Primes × Nat.Primes, Integrable (F pq) := by
    intro pq
    have h := (one_add_cpow_neg_eq_verticalIntegral' hc0 hcs (htpos pq)).1
    have : F pq = fun y : ℝ => ((Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) *
        ((pq.2 : ℕ) : ℂ) ^ (-s)) *
        (KerS s (c + y * I) *
          ((((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I))) :=
      funext (hFeq pq)
    rw [this]
    exact h.const_mul _
  -- Step A': each pair term of `T` is the vertical integral of `F pq`
  have hterm : ∀ pq : Nat.Primes × Nat.Primes,
      (Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) *
        ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ)) ^ (-s) =
      (1 / (2 * Real.pi * I)) * (I * ∫ y : ℝ, F pq y) := by
    intro pq
    have h := (one_add_cpow_neg_eq_verticalIntegral' hc0 hcs (htpos pq)).2
    rw [add_cpow_primes, h, VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul]
    simp_rw [hFeq pq]
    rw [integral_const_mul]
    ring
  -- Step C: summability of the `L¹` norms
  set a : Nat.Primes → ℝ := fun p => ‖qt p (c : ℂ)‖ with ha
  set b : Nat.Primes → ℝ := fun q => ‖qt q ((s.re - c : ℝ) : ℂ)‖ with hb
  have hasum : Summable a := by
    have := summable_norm_Q_terms (z := (c : ℂ)) (by simpa using hc1)
    exact this
  have hbsum : Summable b := by
    have := summable_norm_Q_terms (z := ((s.re - c : ℝ) : ℂ)) (by simp; linarith)
    exact this
  have hnormF : ∀ pq : Nat.Primes × Nat.Primes, ∀ y : ℝ,
      ‖F pq y‖ = ‖KerS s (c + y * I)‖ * (a pq.1 * b pq.2) := by
    intro pq y
    rw [hF]
    dsimp only
    rw [norm_mul, norm_mul]
    simp only [ha, hb, qt]
    rw [norm_Q_term_eq_re pq.1 ((c : ℂ) + y * I), norm_Q_term_eq_re pq.2 (s - ((c : ℂ) + y * I)),
      hre1, hre2]
  have hsumF : Summable fun pq : Nat.Primes × Nat.Primes => ∫ y : ℝ, ‖F pq y‖ := by
    have hab : Summable fun pq : Nat.Primes × Nat.Primes => a pq.1 * b pq.2 :=
      hasum.mul_of_nonneg hbsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine (hab.mul_left (∫ y : ℝ, ‖KerS s (c + y * I)‖)).congr fun pq => ?_
    simp_rw [hnormF pq]
    rw [integral_mul_const]
  -- Step D: the interchange, and the inner sum
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumF
  have hinner : ∀ y : ℝ, ∑' pq : Nat.Primes × Nat.Primes, F pq y =
      KerS s (c + y * I) * Q (c + y * I) * Q (s - (c + y * I)) := by
    intro y
    rw [hF]
    simp only
    rw [tsum_mul_left, mul_assoc]
    congr 1
    rw [Q, Q]
    refine (tsum_mul_tsum_of_summable_norm (f := fun p => qt p (c + y * I))
      (g := fun q => qt q (s - (c + y * I))) ?_ ?_).symm
    · exact summable_norm_Q_terms (by rw [hre1]; exact hc1)
    · exact summable_norm_Q_terms (by rw [hre2]; linarith)
  -- Step E: assemble
  rw [T, VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul]
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_mul_left, hswap]
  simp_rw [hinner]

end GoldbachBoundaries.Paper2.M1
