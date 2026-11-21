import PrimePairNB.Defs

/-!
# The series `P` and `Q` on `Re z > 1`

The Möbius-series identities for `P` and `Q`, and the analytic facts about `P`, `Q` that they rest on.

* `summable_P_terms`, `summable_Q_terms` (and the `norm` versions): the series defining `P`, `Q`
  converge absolutely on `Re z > 1`.
* `P_differentiableOn`, `Q_differentiableOn`: `P`, `Q` are holomorphic on `halfPlane 1`.
* `hasSum_Q_moebius`, `Q_eq_tsum_moebius_zeta`: `Q(z) = ∑_{n ≥ 1} μ(n) A(nz)` with
  `A(w) = ∑ Λ(m) m^{-w} = -ζ'(w)/ζ(w)`.

Method. `P = LSeries 1_{prime}` and `Q = LSeries (log · 1_{prime})`, so holomorphy and `P' = -Q`
come from Mathlib's L-series calculus. For the Möbius identities the justification is absolute convergence of the triple series
`∑_{p, n, j} log p · μ(n) · p^{-n(j+1)z}` (bound: `|p^{-z}| ≤ 1/2` and `n(j+1) ≥ n + j`), which is
summed once with `p` outermost (the inner double sum is `∑_N p^{-Nz} ∑_{d ∣ N} μ(d) = p^{-z}`,
`hasSum_moebius_comp`) and once with `n` outermost (the inner sum is `A(nz)` after reindexing
prime powers `p^{j+1}`, `tsum_eq_tsum_primes_pow`).
-/

noncomputable section

open Complex Filter Topology Set ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

/-! ## 1. `P`, `Q` as L-series; summability, holomorphy, `P' = -Q` -/

/-- The indicator function of the primes, as an `ℕ → ℂ` coefficient sequence. -/
def primeInd (n : ℕ) : ℂ := if n.Prime then 1 else 0

lemma term_primeInd_prime (z : ℂ) (p : Nat.Primes) :
    term primeInd z p = ((p : ℕ) : ℂ) ^ (-z) := by
  have hp : (p : ℕ).Prime := p.2
  simp [term, primeInd, hp, hp.ne_zero, cpow_neg]

lemma term_logMul_primeInd_prime (z : ℂ) (p : Nat.Primes) :
    term (logMul primeInd) z p = (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z) := by
  have hp : (p : ℕ).Prime := p.2
  simp [term, logMul, primeInd, hp, hp.ne_zero, cpow_neg, div_eq_mul_inv]

lemma support_term_primeInd (z : ℂ) :
    Function.support (term primeInd z) ⊆ {n | n.Prime} := by
  intro n hn
  simp only [mem_ofPred_eq]
  by_contra h
  simp [term, primeInd, h] at hn

lemma support_term_logMul_primeInd (z : ℂ) :
    Function.support (term (logMul primeInd) z) ⊆ {n | n.Prime} := by
  intro n hn
  simp only [mem_ofPred_eq]
  by_contra h
  simp [term, logMul, primeInd, h] at hn

lemma P_eq_LSeries : P = LSeries primeInd := by
  funext z
  rw [LSeries, ← tsum_subtype_eq_of_support_subset (support_term_primeInd z)]
  exact tsum_congr fun p => (term_primeInd_prime z p).symm

lemma Q_eq_LSeries : Q = LSeries (logMul primeInd) := by
  funext z
  rw [LSeries, ← tsum_subtype_eq_of_support_subset (support_term_logMul_primeInd z)]
  exact tsum_congr fun p => (term_logMul_primeInd_prime z p).symm

lemma abscissa_primeInd_le : abscissaOfAbsConv primeInd ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by
    unfold primeInd; split_ifs <;> simp⟩

lemma abscissa_lt_of_mem {z : ℂ} (hz : z ∈ halfPlane 1) : abscissaOfAbsConv primeInd < z.re :=
  lt_of_le_of_lt abscissa_primeInd_le (by exact_mod_cast hz)

lemma abscissa_logMul_lt_of_mem {z : ℂ} (hz : z ∈ halfPlane 1) :
    abscissaOfAbsConv (logMul primeInd) < z.re := by
  rw [LSeries.abscissaOfAbsConv_logMul]; exact abscissa_lt_of_mem hz

theorem summable_P_terms {z : ℂ} (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-z)) := by
  have h : Summable (term primeInd z) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (abscissa_lt_of_mem hz)
  exact (h.subtype {n | n.Prime}).congr fun p => term_primeInd_prime z p

theorem summable_Q_terms {z : ℂ} (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)) := by
  have h : Summable (term (logMul primeInd) z) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (abscissa_logMul_lt_of_mem hz)
  exact (h.subtype {n | n.Prime}).congr fun p => term_logMul_primeInd_prime z p

theorem summable_norm_P_terms {z : ℂ} (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-z)‖) :=
  summable_norm_iff.mpr (summable_P_terms hz)

theorem summable_norm_Q_terms {z : ℂ} (hz : 1 < z.re) :
    Summable (fun p : Nat.Primes => ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖) :=
  summable_norm_iff.mpr (summable_Q_terms hz)

theorem P_differentiableOn : DifferentiableOn ℂ P (halfPlane 1) := by
  rw [P_eq_LSeries]
  exact (LSeries_differentiableOn _).mono fun z hz => abscissa_lt_of_mem hz

theorem Q_differentiableOn : DifferentiableOn ℂ Q (halfPlane 1) := by
  rw [Q_eq_LSeries]
  exact (LSeries_differentiableOn _).mono fun z hz => abscissa_logMul_lt_of_mem hz

theorem hasDerivAt_P {z : ℂ} (hz : z ∈ halfPlane 1) : HasDerivAt P (-Q z) z := by
  rw [P_eq_LSeries, Q_eq_LSeries]
  exact LSeries_hasDerivAt (abscissa_lt_of_mem hz)

/-! ## 2. Möbius inversion in one variable -/

lemma sum_divisors_mu (N : ℕ) : ∑ d ∈ N.divisors, mu d = if N = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f N) (coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [coe_mul_zeta_apply, intCoe_apply, one_apply] at h
  exact h

/-- Möbius inversion along `N = n (j + 1)`: if the double series converges (unconditionally),
`∑_{n, j} μ(n) c(n (j + 1)) = c(1)`, because the terms with `n (j + 1) = N` sum to
`c(N) ∑_{d ∣ N} μ(d) = c(N) [N = 1]`. -/
theorem hasSum_moebius_comp {c : ℕ → ℂ}
    (hs : Summable fun x : ℕ × ℕ => mu x.1 * c (x.1 * (x.2 + 1))) :
    HasSum (fun x : ℕ × ℕ => mu x.1 * c (x.1 * (x.2 + 1))) (c 1) := by
  set F : ℕ × ℕ → ℂ := fun x => if x.2 = 0 then 0 else mu x.1 * c (x.1 * x.2) with hFdef
  set g : ℕ × ℕ → ℕ × ℕ := fun x => (x.1, x.2 + 1) with hgdef
  have hg : Function.Injective g := by
    intro x y h
    simp only [g, Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  have hF0 : ∀ x ∉ range g, F x = 0 := by
    intro x hx
    have : x.2 = 0 := by
      by_contra h2
      exact hx ⟨(x.1, x.2 - 1), Prod.ext rfl (by simp [g]; omega)⟩
    simp [F, this]
  have hFg : F ∘ g = fun x : ℕ × ℕ => mu x.1 * c (x.1 * (x.2 + 1)) := by
    funext x; simp [F, g]
  rw [← hFg, hg.hasSum_iff hF0]
  rw [← hFg, hg.summable_iff hF0] at hs
  have hfib := hs.hasSum.tsum_fiberwise (fun x : ℕ × ℕ => x.1 * x.2)
  have hval : (fun N : ℕ => ∑' b : (fun x : ℕ × ℕ => x.1 * x.2) ⁻¹' {N}, F b) =
      fun N => if N = 1 then c 1 else 0 := by
    funext N
    by_cases hN : N = 0
    · subst hN
      have : ∀ b : (fun x : ℕ × ℕ => x.1 * x.2) ⁻¹' {0}, F b = 0 := by
        rintro ⟨b, hb⟩
        simp only [mem_preimage, mem_singleton_iff, mul_eq_zero] at hb
        rcases hb with hb | hb <;> simp [F, hb]
      simp [tsum_congr this]
    · have hset : (fun x : ℕ × ℕ => x.1 * x.2) ⁻¹' {N} = ↑N.divisorsAntidiagonal := by
        ext x; simp [Nat.mem_divisorsAntidiagonal, hN]
      rw [hset, Finset.tsum_subtype']
      have : ∀ x ∈ N.divisorsAntidiagonal, F x = mu x.1 * c N := by
        intro x hx
        have hx' := Nat.mem_divisorsAntidiagonal.mp hx
        have h2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
        simp [F, h2, hx'.1]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
        Nat.sum_divisorsAntidiagonal (f := fun a _ => mu a), sum_divisors_mu]
      split_ifs with h1 <;> simp [h1]
  rw [hval] at hfib
  have h1 : HasSum (fun N : ℕ => if N = 1 then c 1 else 0) (c 1) := hasSum_ite_eq 1 (c 1)
  rw [h1.unique hfib]
  exact hs.hasSum

/-! ## 3. Reindexing prime powers; the triple-sum interchange -/

/-- Reindexing over prime powers, no summability needed. -/
lemma tsum_eq_tsum_primes_pow {f : ℕ → ℂ} (hf : Function.support f ⊆ {n | IsPrimePow n}) :
    ∑' m, f m = ∑' pj : Nat.Primes × ℕ, f ((pj.1 : ℕ) ^ (pj.2 + 1)) := by
  rw [← tsum_subtype_eq_of_support_subset hf]
  change ∑' m : {n : ℕ // IsPrimePow n}, f m = _
  rw [← Nat.Primes.prodNatEquiv.tsum_eq]
  rfl

lemma summable_half_pow_pred : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n - 1)) := by
  rw [← summable_nat_add_iff 1]
  simpa using summable_geometric_two

/-- The triple-sum interchange behind the Möbius-series identities. -/
theorem hasSum_moebius_triple (a : Nat.Primes → ℂ) (c : Nat.Primes → ℕ → ℂ) (b : Nat.Primes → ℝ)
    (hb0 : ∀ p, 0 ≤ b p) (hB : Summable fun p => ‖a p‖ * b p)
    (hbound : ∀ p n j, ‖mu n * c p (n * (j + 1))‖ ≤ b p * ((1 / 2 : ℝ) ^ (n - 1) * (1 / 2) ^ j))
    (hcore : ∀ p, HasSum (fun x : ℕ × ℕ => mu x.1 * c p (x.1 * (x.2 + 1))) (c p 1)) :
    HasSum (fun n : ℕ => mu n * ∑' pj : Nat.Primes × ℕ, a pj.1 * c pj.1 (n * (pj.2 + 1)))
      (∑' p, a p * c p 1) := by
  set T : Nat.Primes × (ℕ × ℕ) → ℂ := fun x => a x.1 * (mu x.2.1 * c x.1 (x.2.1 * (x.2.2 + 1)))
  have hG : Summable (fun nj : ℕ × ℕ => (1 / 2 : ℝ) ^ (nj.1 - 1) * (1 / 2) ^ nj.2) :=
    summable_half_pow_pred.mul_of_nonneg summable_geometric_two (fun _ => by positivity)
      (fun _ => by positivity)
  have hTs : Summable T := by
    refine Summable.of_norm_bounded
      ((hB.mul_of_nonneg hG (fun p => mul_nonneg (norm_nonneg _) (hb0 p))
        (fun _ => by positivity))) ?_
    rintro ⟨p, n, j⟩
    have := hbound p n j
    simp only [T, norm_mul] at this ⊢
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  -- p outer
  have h1 : HasSum (fun p => a p * c p 1) (∑' x, T x) :=
    hTs.hasSum.prod_fiberwise fun p => (hcore p).mul_left (a p)
  -- n outer
  let e : ℕ × (Nat.Primes × ℕ) ≃ Nat.Primes × (ℕ × ℕ) :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun y => (y.2.1, (y.1, y.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hTe : HasSum (T ∘ e) (∑' x, T x) := e.hasSum_iff.mpr hTs.hasSum
  have h2 := hTe.prod_fiberwise fun n => (hTe.summable.prod_factor n).hasSum
  rw [h1.tsum_eq.symm] at h2
  convert h2 using 2 with n
  rw [← tsum_mul_left]
  refine tsum_congr fun pj => ?_
  simp only [T, e, Function.comp, Equiv.coe_fn_mk]
  ring

/-! ## 4. Bounds and prime-power terms -/

lemma norm_mu_le_one (n : ℕ) : ‖mu n‖ ≤ 1 := by
  simp only [mu, norm_intCast]
  exact_mod_cast abs_moebius_le_one

lemma pow_le_half_bound {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    r ^ (n * (j + 1)) ≤ r * ((1 / 2 : ℝ) ^ (n - 1) * (1 / 2) ^ j) := by
  have hle : 1 + (n - 1) + j ≤ n * (j + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    simp only [Nat.add_sub_cancel]; nlinarith
  calc r ^ (n * (j + 1)) ≤ r ^ (1 + (n - 1) + j) :=
        pow_le_pow_of_le_one hr0 (by linarith) hle
    _ = r * (r ^ (n - 1) * r ^ j) := by rw [pow_add, pow_add, pow_one]; ring
    _ ≤ r * ((1 / 2 : ℝ) ^ (n - 1) * (1 / 2) ^ j) := by gcongr

lemma term_vonMangoldt_prime_pow (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    term (fun n => (Λ n : ℂ)) s ((p : ℕ) ^ (k + 1)) =
      (Real.log (p : ℕ) : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) := by
  have hp : (p : ℕ).Prime := p.2
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    vonMangoldt_apply_prime hp, Nat.cast_pow, ← natCast_cpow_natCast_mul, cpow_nat_mul,
    cpow_neg, inv_pow, div_eq_mul_inv]

lemma summable_G : Summable (fun nj : ℕ × ℕ => (1 / 2 : ℝ) ^ (nj.1 - 1) * (1 / 2) ^ nj.2) :=
  summable_half_pow_pred.mul_of_nonneg summable_geometric_two (fun _ => by positivity)
    (fun _ => by positivity)

lemma support_term_vonMangoldt (s : ℂ) :
    Function.support (term (fun n => (Λ n : ℂ)) s) ⊆ {n | IsPrimePow n} := by
  intro n hn
  simp only [mem_ofPred_eq]
  by_contra h
  simp [term, vonMangoldt_eq_zero_iff.mpr h] at hn

/-- `A(s) = ∑ Λ(m) m^{-s}` as a sum over prime powers `p^{j+1}` (any `s`; both sides are `tsum`s
of the same family up to reindexing). -/
lemma LSeries_vonMangoldt_eq_tsum_primes (s : ℂ) :
    L ↗Λ s = ∑' pj : Nat.Primes × ℕ,
      (Real.log (pj.1 : ℕ) : ℂ) * (((pj.1 : ℕ) : ℂ) ^ (-s)) ^ (pj.2 + 1) := by
  rw [LSeries, tsum_eq_tsum_primes_pow (support_term_vonMangoldt s)]
  exact tsum_congr fun pj => term_vonMangoldt_prime_pow s pj.1 pj.2

lemma prime_cpow_pow_mul (z : ℂ) (p : Nat.Primes) (n j : ℕ) :
    (((p : ℕ) : ℂ) ^ (-z)) ^ (n * (j + 1)) = (((p : ℕ) : ℂ) ^ (-((n : ℂ) * z))) ^ (j + 1) := by
  rw [pow_mul, ← cpow_nat_mul, mul_neg]

/-! ## 5. The Möbius-series identities -/

/-- **Second Möbius identity** (`Q(z) = ∑_{n≥1} μ(n) A(nz)` for `Re z > 1`),
with `A = L ↗Λ` the von Mangoldt L-series. The `n = 0` term is `μ(0) · _ = 0`. -/
theorem hasSum_Q_moebius {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n : ℕ => mu n * L ↗Λ (n * z)) (Q z) := by
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-z) with hw_def
  have hw : ∀ p, ‖w p‖ ≤ 1 / 2 := fun p => norm_prime_cpow_le_one_half p hz
  have hbound : ∀ p n j, ‖mu n * w p ^ (n * (j + 1))‖ ≤
      ‖w p‖ * ((1 / 2 : ℝ) ^ (n - 1) * (1 / 2) ^ j) := by
    intro p n j
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [mu, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, norm_pow]
      calc _ ≤ 1 * ‖w p‖ ^ (n * (j + 1)) := by gcongr; exact norm_mu_le_one n
        _ ≤ _ := by rw [one_mul]; exact pow_le_half_bound (norm_nonneg _) (hw p) hn j
  have hsum : ∀ p, Summable (fun x : ℕ × ℕ => mu x.1 * w p ^ (x.1 * (x.2 + 1))) := fun p =>
    Summable.of_norm_bounded (summable_G.mul_left ‖w p‖) (fun x => hbound p x.1 x.2)
  have hB : Summable fun p : Nat.Primes => ‖(Real.log (p : ℕ) : ℂ)‖ * ‖w p‖ := by
    simpa only [norm_mul] using summable_norm_Q_terms hz
  have h := hasSum_moebius_triple (fun p => (Real.log (p : ℕ) : ℂ)) (fun p N => w p ^ N)
    (fun p => ‖w p‖) (fun _ => norm_nonneg _) hB hbound
    (fun p => hasSum_moebius_comp (hsum p))
  simp only [pow_one] at h
  rw [show Q z = ∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * w p from rfl]
  convert h using 2 with n
  rw [LSeries_vonMangoldt_eq_tsum_primes]
  congr 1
  refine tsum_congr fun pj => ?_
  simp only [hw_def, prime_cpow_pow_mul]

lemma one_lt_re_natCast_mul {z : ℂ} (hz : 1 < z.re) {n : ℕ} (hn : n ≠ 0) :
    1 < ((n : ℂ) * z).re := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
  nlinarith

/-- **Second Möbius identity**, with `A(w) = -ζ'(w)/ζ(w)` written via Mathlib's
`riemannZeta` and `deriv`. -/
theorem hasSum_Q_moebius_zeta {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n : ℕ => mu n * (-deriv riemannZeta (n * z) / riemannZeta (n * z))) (Q z) := by
  convert hasSum_Q_moebius hz using 2 with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (one_lt_re_natCast_mul hz hn)]

theorem Q_eq_tsum_moebius_zeta {z : ℂ} (hz : 1 < z.re) :
    Q z = ∑' n : ℕ, mu n * (-deriv riemannZeta (n * z) / riemannZeta (n * z)) :=
  (hasSum_Q_moebius_zeta hz).tsum_eq.symm

/-! ## 6. Absolute convergence of the double series; `A(s) = ∑_j Q(js)` -/

lemma summable_vonMangoldt_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun m : ℕ => Λ m * (m : ℝ) ^ (-x)) := by
  have h : Summable (term (fun n => (Λ n : ℂ)) (x : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hx)
  refine (summable_norm_iff.mpr h).congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp only [norm_term_eq, hm, ↓reduceIte]
    rw [ofReal_re, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]

end GoldbachBoundaries
