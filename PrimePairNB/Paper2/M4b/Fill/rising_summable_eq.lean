import PrimePairNB.Paper2.M4b.MB
import PrimePairNB.Paper2.M4b.Fill.ACommonRising

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Absolute convergence and the integral identity for `Wrise`** (`σ > 2`). A line `c ∈ (1, σ - 1)` exists
(`c = σ/2`). For each `(i, j)`: `p^iq^j(p+q)^{-(s+i+j)} = q^{-s}·(p/q)^i(1 + p/q)^{-(s+i+j)}` for primes (positive
reals, `Complex.mul_cpow_ofReal_nonneg`, as `add_cpow_primes` in `T_eq_verticalIntegral'_KerS`), and
`mellinInv_kMB` with `a = 1`, `μ = i`, `ν = s + i + j` (`0 < c + i < σ + i + j`) gives `f(t) = t^i(1+t)^{-(s+i+j)}`
the kernel `kMB 1 i (s+i+j) z = Γ(z+i)Γ(s-z+j)/Γ(s+i+j)` (`KerS`, `(z + i)/1`, `s + i + j - (z + i) = s - z + j`).
`tsum_eq_verticalIntegral'_of_mellin` (with `L = s`) gives, per `(i, j)`, summability, integrability and the identity.
Multiply by `c_{ij}(s)` and sum over the finite range: `Summable.of_norm_bounded` against `∑_{ij} ‖term_{ij}‖`
(`norm_sum_le`), `tsum_finsetSum`-type interchange (`Summable.tsum_finsetSum` / `tsum_sum`), and linearity of
`VerticalIntegral'` (`integral_finset_sum` with the per-term integrability). -/
theorem rising_summable_eq {ω : ℕ → ℝ} (hω : PrimeWeight ω) (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ) {s : ℂ}
    (hs : 2 < s.re) :
    Summable (fun pq : Nat.Primes × Nat.Primes => ‖wtd ω (Wrise N cf) s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    ∀ c : ℝ, 1 < c → c < s.re - 1 →
      Integrable (fun y : ℝ =>
        krise N cf (c + y * I) s * primeSum ω (c + y * I) * primeSum ω (s - (c + y * I))) ∧
      Dser (wtd ω (Wrise N cf)) s =
        VerticalIntegral' (fun z => krise N cf z s * primeSum ω z * primeSum ω (s - z)) c := by
  let V : ℕ → ℕ → Nat.Primes × Nat.Primes → ℂ := fun i j pq =>
    cf i j s * ((ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ) *
      (((pq.1 : ℕ) : ℂ) ^ i * ((pq.2 : ℕ) : ℂ) ^ j *
        (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j))))
  let K : ℕ → ℕ → ℂ → ℂ := fun i j z =>
    cf i j s * ((Gamma (z + i) * Gamma (s - z + j) / Gamma (s + i + j)) *
      primeSum ω z * primeSum ω (s - z))
  have hv : ∀ pq : Nat.Primes × Nat.Primes,
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, V i j pq) =
        wtd ω (Wrise N cf) s (pq.1 : ℕ) (pq.2 : ℕ) := by
    intro pq
    simp only [wtd, Wrise, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [V]
    ring
  have hk : ∀ z : ℂ,
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, K i j z) =
        krise N cf z s * primeSum ω z * primeSum ω (s - z) := by
    intro z
    simp only [krise, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [K]
    ring
  have hall : ∀ c : ℝ, 1 < c → c < s.re - 1 →
      Summable (fun pq : Nat.Primes × Nat.Primes => ‖wtd ω (Wrise N cf) s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
      Integrable (fun y : ℝ => krise N cf (c + y * I) s *
        primeSum ω (c + y * I) * primeSum ω (s - (c + y * I))) ∧
      Dser (wtd ω (Wrise N cf)) s =
        VerticalIntegral' (fun z => krise N cf z s * primeSum ω z * primeSum ω (s - z)) c := by
    intro c hc1 hc2
    have hm : ∀ i j : ℕ, Summable (fun pq => ‖V i j pq‖) ∧
        Integrable (fun y : ℝ => K i j (c + y * I)) ∧
        (∑' pq, V i j pq) = VerticalIntegral' (K i j) c := by
      intro i j
      obtain ⟨hV, hK, heq⟩ := A_rising_monomial hω i j hc1 hc2
      refine ⟨?_, hK.const_mul (cf i j s), ?_⟩
      · simpa only [V, norm_mul] using hV.mul_left ‖cf i j s‖
      · dsimp [V, K]
        rw [tsum_mul_left, heq]
        unfold VerticalIntegral' VerticalIntegral
        simp only [smul_eq_mul]
        rw [integral_const_mul]
        ring
    have hsum := A_MB_sum (Finset.range N) (fun i pq => ∑ j ∈ Finset.range N, V i j pq)
      (fun i z => ∑ j ∈ Finset.range N, K i j z) c
      (fun i hi => A_MB_sum (Finset.range N) (V i) (K i) c (fun j hj => hm i j))
    simpa only [hv, hk, Dser] using hsum
  exact ⟨(hall (s.re / 2) (by linarith) (by linarith)).1,
    fun c hc1 hc2 => (hall c hc1 hc2).2⟩

end GoldbachBoundaries.Paper2.M4b
