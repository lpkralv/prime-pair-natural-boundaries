import PrimePairNB.Paper2.M4b.Defs
import PrimePairNB.Paper2.M1.Fill.KernelCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

-- Prime-power identities adapted from `M1/Fill/T_eq_verticalIntegral'_KerS.lean`.

/-- `(p/q)^{-w} = p^{-w} q^{w}` for primes `p, q`. -/
lemma A_div_cpow_primes (p q : Nat.Primes) (w : ℂ) :
    ((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (-w) =
      ((p : ℕ) : ℂ) ^ (-w) * ((q : ℕ) : ℂ) ^ w := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have harg : (((q : ℕ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hp (inv_nonneg.mpr hq.le), ofReal_inv,
    inv_cpow _ _ harg, ← cpow_neg, neg_neg, ofReal_natCast, ofReal_natCast]

/-- `(p + q)^{-s} = q^{-s} (1 + p/q)^{-s}`. -/
lemma A_add_cpow_primes (p q : Nat.Primes) (s : ℂ) :
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

/-- The norm of a weighted prime term is constant on vertical lines. -/
lemma A_norm_term_re (ω : ℕ → ℝ) (p : Nat.Primes) (z : ℂ) :
    ‖(ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ =
      ‖(ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z.re : ℂ))‖ := by
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos p.prop.pos,
    norm_natCast_cpow_of_pos p.prop.pos]
  simp

/-- Homogeneity of one rising weight at positive prime arguments. -/
lemma A_rising_term (i j : ℕ) (s : ℂ) (p q : Nat.Primes) :
    ((p : ℕ) : ℂ) ^ i * ((q : ℕ) : ℂ) ^ j *
      (((p : ℕ) + (q : ℕ) : ℕ) : ℂ) ^ (-(s + i + j)) =
    ((q : ℕ) : ℂ) ^ (-s) *
      (((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (i : ℂ) *
        ((1 + ((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (-(s + i + j))) := by
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have hsplit : ((q : ℕ) : ℂ) ^ (-s) =
      ((q : ℕ) : ℂ) ^ (-(s + i + j)) * ((q : ℕ) : ℂ) ^ i * ((q : ℕ) : ℂ) ^ j := by
    simp only [← cpow_natCast]
    rw [← cpow_add _ _ hq, ← cpow_add _ _ hq]
    congr 1
    ring
  rw [A_add_cpow_primes, hsplit, cpow_natCast]
  push_cast
  rw [div_pow]
  field_simp

lemma A_kMB_rising (i j : ℕ) (s z : ℂ) :
    kMB 1 (i : ℂ) (s + i + j) z = Gamma (z + i) * Gamma (s - z + j) / Gamma (s + i + j) := by
  simp only [kMB, Nat.cast_one, inv_one, div_one, one_mul, KerS]
  congr 2
  congr 1
  ring

/-- Finite linearity, keeping absolute convergence and integrability explicit. -/
lemma A_MB_sum {ι : Type*} (S : Finset ι)
    (V : ι → Nat.Primes × Nat.Primes → ℂ) (K : ι → ℂ → ℂ) (c : ℝ)
    (h : ∀ i ∈ S, Summable (fun pq => ‖V i pq‖) ∧
      Integrable (fun y : ℝ => K i (c + y * I)) ∧
      (∑' pq, V i pq) = VerticalIntegral' (K i) c) :
    Summable (fun pq => ‖∑ i ∈ S, V i pq‖) ∧
      Integrable (fun y : ℝ => ∑ i ∈ S, K i (c + y * I)) ∧
      (∑' pq, ∑ i ∈ S, V i pq) = VerticalIntegral' (fun z => ∑ i ∈ S, K i z) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [VerticalIntegral', VerticalIntegral]
  | @insert i S hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    refine ⟨?_, h₁.2.1.add h₂.2.1, ?_⟩
    · exact (h₁.1.add h₂.1).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
    · rw [h₁.1.of_norm.tsum_add h₂.1.of_norm, h₁.2.2, h₂.2.2]
      unfold VerticalIntegral' VerticalIntegral
      simp only [smul_eq_mul]
      rw [integral_add h₁.2.1 h₂.2.1]
      ring

/-- The powers in a rising monomial cost at most the same power of `p+q`. -/
lemma A_norm_rising_le (i j : ℕ) (s : ℂ) (p q : Nat.Primes) {σ : ℝ}
    (hσ : σ ≤ s.re) :
    ‖((p : ℕ) : ℂ) ^ i * ((q : ℕ) : ℂ) ^ j *
      (((p : ℕ) + (q : ℕ) : ℕ) : ℂ) ^ (-(s + i + j))‖ ≤
      (((p : ℕ) + (q : ℕ) : ℕ) : ℝ) ^ (-σ) := by
  let n : ℝ := ((p : ℕ) + (q : ℕ) : ℕ)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (by have := p.prop.pos; omega : 0 < (p : ℕ) + (q : ℕ))
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (by have := p.prop.pos; omega : 1 ≤ (p : ℕ) + (q : ℕ))
  have hp : ((p : ℕ) : ℝ) ≤ n := by dsimp [n]; exact_mod_cast Nat.le_add_right (p : ℕ) (q : ℕ)
  have hq : ((q : ℕ) : ℝ) ≤ n := by dsimp [n]; exact_mod_cast Nat.le_add_left (q : ℕ) (p : ℕ)
  have hpow : ((p : ℕ) : ℝ) ^ i * ((q : ℕ) : ℝ) ^ j ≤ n ^ (i + j) := by
    rw [pow_add]
    gcongr
  have he : (-(s + i + j)).re = -s.re + -((i + j : ℕ) : ℝ) := by simp; ring
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
    norm_natCast_cpow_of_pos (by have := p.prop.pos; omega), he]
  change ((p : ℕ) : ℝ) ^ i * ((q : ℕ) : ℝ) ^ j * n ^ (-s.re + -((i + j : ℕ) : ℝ)) ≤ n ^ (-σ)
  rw [Real.rpow_add hn, Real.rpow_neg hn.le ((i + j : ℕ) : ℝ), Real.rpow_natCast]
  calc ((p : ℕ) : ℝ) ^ i * ((q : ℕ) : ℝ) ^ j * (n ^ (-s.re) * (n ^ (i + j))⁻¹)
      = (((p : ℕ) : ℝ) ^ i * ((q : ℕ) : ℝ) ^ j / n ^ (i + j)) * n ^ (-s.re) := by ring
    _ ≤ 1 * n ^ (-s.re) := by
      apply mul_le_mul_of_nonneg_right ((div_le_one (pow_pos hn _)).mpr hpow)
      positivity
    _ ≤ n ^ (-σ) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hσ)

lemma A_summable_finset {ι κ : Type*} (S : Finset ι) (f : ι → κ → ℝ)
    (h : ∀ i ∈ S, Summable (f i)) : Summable (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GoldbachBoundaries.Paper2.M4b
