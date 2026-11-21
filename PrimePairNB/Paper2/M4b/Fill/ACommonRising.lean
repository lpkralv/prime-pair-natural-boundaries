import PrimePairNB.Paper2.M4b.Fill.ACommon
import PrimePairNB.Paper2.M4b.Fill.mellinInv_kMB
import PrimePairNB.Paper2.M4b.Fill.tsum_eq_verticalIntegral'_of_mellin

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

-- Split from `ACommon.lean`: this lemma uses `mellinInv_kMB` and `tsum_eq_verticalIntegral'_of_mellin`, whose
-- proofs use `ACommon`.

/-- One rising monomial, with its Mellin--Barnes integral. -/
lemma A_rising_monomial {ω : ℕ → ℝ} (hω : PrimeWeight ω) (i j : ℕ) {s : ℂ}
    {c : ℝ} (hc1 : 1 < c) (hc2 : c < s.re - 1) :
    let V := fun pq : Nat.Primes × Nat.Primes =>
      (ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ) *
      (((pq.1 : ℕ) : ℂ) ^ i * ((pq.2 : ℕ) : ℂ) ^ j *
        (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j)))
    let K := fun z : ℂ =>
      (Gamma (z + i) * Gamma (s - z + j) / Gamma (s + i + j)) *
        primeSum ω z * primeSum ω (s - z)
    Summable (fun pq => ‖V pq‖) ∧
      Integrable (fun y : ℝ => K (c + y * I)) ∧
      (∑' pq, V pq) = VerticalIntegral' K c := by
  dsimp only
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (i : ℂ) *
    ((1 + t : ℝ) : ℂ) ^ (-(s + i + j))
  have h1 : 0 < (c + (i : ℂ).re) / (1 : ℕ) := by simp; positivity
  have h2 : (c + (i : ℂ).re) / (1 : ℕ) < (s + i + j).re := by
    simp only [Nat.cast_one, div_one, natCast_re, add_re]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hk := (mellinInv_kMB (a := 1) (by norm_num) (i : ℂ) (s + i + j)
    h1 h2 (t := 1) (by norm_num)).1
  have hf : ∀ t : ℝ, 0 < t → f t =
      VerticalIntegral' (fun z => kMB 1 (i : ℂ) (s + i + j) z * (t : ℂ) ^ (-z)) c := by
    intro t ht
    simpa only [f, pow_one] using
      (mellinInv_kMB (a := 1) (by norm_num) (i : ℂ) (s + i + j) h1 h2 ht).2
  have h := tsum_eq_verticalIntegral'_of_mellin hω hc1 hc2 hk hf
  have hv : (fun pq : Nat.Primes × Nat.Primes =>
      (ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ) * ((pq.2 : ℕ) : ℂ) ^ (-s) *
      f (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ))) =
      fun pq => (ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ) *
      (((pq.1 : ℕ) : ℂ) ^ i * ((pq.2 : ℕ) : ℂ) ^ j *
        (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j))) := by
    funext pq
    rw [A_rising_term]
    dsimp [f]
    ring
  simp_rw [A_kMB_rising] at h
  rw [hv] at h
  exact ⟨h.1.congr (fun pq => congrArg norm (congrFun hv pq)), h.2⟩

end GoldbachBoundaries.Paper2.M4b
