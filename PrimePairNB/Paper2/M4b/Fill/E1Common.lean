import PrimePairNB.Paper2.M4b.Rising

noncomputable section
open Complex Filter Topology Set MeasureTheory
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma E1_integral_congr {f g : ℂ → ℂ} {c : ℝ}
    (h : ∀ y : ℝ, f (c + y * I) = g (c + y * I)) :
    VerticalIntegral' f c = VerticalIntegral' g c := by
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  exact integral_congr_ae (Filter.Eventually.of_forall h)

lemma E1_cpow_real (n : ℕ) (x : ℝ) : (((n : ℂ) ^ (x : ℂ))).im = 0 := by
  have he := Complex.ofReal_cpow (Nat.cast_nonneg n : (0 : ℝ) ≤ n) x
  simpa using congrArg Complex.im he.symm

lemma E1_dser_real {W : ℂ → ℕ → ℕ → ℂ} {x : ℝ}
    (hr : ∀ pq : Nat.Primes × Nat.Primes, (W x (pq.1 : ℕ) (pq.2 : ℕ)).im = 0) :
    (Dser W x).im = 0 := by
  unfold Dser
  by_cases h : Summable (fun pq : Nat.Primes × Nat.Primes => W x (pq.1 : ℕ) (pq.2 : ℕ))
  · rw [Complex.im_tsum h]
    simp [hr]
  · rw [tsum_eq_zero_of_not_summable h, zero_im]

lemma E1_hypR_rising {ω : ℕ → ℝ} (hω : PrimeWeight ω)
    (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ)
    (hcf : ∀ i j, DifferentiableOn ℂ (cf i j) (halfPlane 2))
    (W : ℂ → ℕ → ℕ → ℂ) (k : ℂ → ℂ → ℂ)
    (hW : ∀ s : ℂ, ∀ pq : Nat.Primes × Nat.Primes,
      W s (pq.1 : ℕ) (pq.2 : ℕ) = wtd ω (Wrise N cf) s (pq.1 : ℕ) (pq.2 : ℕ))
    (hk : ∀ z s : ℂ, 0 < z.re → 0 < (s - z).re → k z s = krise N cf z s)
    (hr : ∀ x : ℝ, 2 < x → ∀ pq : Nat.Primes × Nat.Primes,
      (W x (pq.1 : ℕ) (pq.2 : ℕ)).im = 0) : HypR Aff.idL k W (primeSum ω) := by
  have hd : Dser W = Dser (wtd ω (Wrise N cf)) := by
    funext s
    exact dser_congr (hW s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [idL_RL_eq] at hs
    simpa only [← hW s] using (rising_summable_eq hω N cf hs).1
  · rw [hd, idL_RL_eq]
    exact rising_differentiableOn hω N cf hcf
  · intro x hx
    rw [idL_RL_eq] at hx
    exact E1_dser_real (hr x (by simpa [halfPlane] using hx))
  · intro s hs c hc1 hc2
    have hs' : 2 < s.re := by simpa [Aff.RL, M4a.app_idL] using hs.1
    rw [M4a.app_idL] at hc2
    rw [hd, ((rising_summable_eq hω N cf hs').2 c hc1 hc2).2]
    apply E1_integral_congr
    intro y
    rw [hk _ _ (by simp; linarith) (by simp; linarith), M4a.app_idL]

lemma E1_differentiable_halfPlane {W : ℂ → ℕ → ℕ → ℂ} {a : ℝ}
    (hsum : ∀ s : ℂ, a < s.re → Summable fun pq : Nat.Primes × Nat.Primes =>
      ‖W s (pq.1 : ℕ) (pq.2 : ℕ)‖)
    (hterm : ∀ pq : Nat.Primes × Nat.Primes,
      DifferentiableOn ℂ (fun s => W s (pq.1 : ℕ) (pq.2 : ℕ)) (halfPlane a))
    (hbound : ∀ s : ℂ, ∀ x : ℝ, a < x → x ≤ s.re → ∀ pq : Nat.Primes × Nat.Primes,
      ‖W s (pq.1 : ℕ) (pq.2 : ℕ)‖ ≤ ‖W x (pq.1 : ℕ) (pq.2 : ℕ)‖) :
    DifferentiableOn ℂ (Dser W) (halfPlane a) := by
  apply differentiableOn_dser (isOpen_lt continuous_const Complex.continuous_re) hterm
  intro s₀ hs₀
  have hs₀' : a < s₀.re := hs₀
  let x : ℝ := (a + s₀.re) / 2
  have hx : a < x := by dsimp [x]; linarith
  refine ⟨{s : ℂ | x < s.re},
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [x]; linarith),
    fun pq => ‖W x (pq.1 : ℕ) (pq.2 : ℕ)‖, hsum x (by simpa using hx), ?_⟩
  intro s hs pq
  exact hbound s x hx (le_of_lt hs) pq

lemma E1_MB_pair (a : ℕ) (ha : 0 < a) (μ ν L : ℂ) (c : ℝ)
    (hc1 : 1 < c) (hc2 : c < L.re - 1)
    (h1 : 0 < (c + μ.re) / a) (h2 : (c + μ.re) / a < ν.re) :
    Summable (fun pq : Nat.Primes × Nat.Primes =>
      ‖((pq.2 : ℕ) : ℂ) ^ (-L) *
        ((((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) : ℝ) : ℂ) ^ μ *
        (((1 + (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ)) ^ a : ℝ)) : ℂ) ^ (-ν)‖) ∧
    (∑' pq : Nat.Primes × Nat.Primes,
      ((pq.2 : ℕ) : ℂ) ^ (-L) *
        ((((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ) : ℝ) : ℂ) ^ μ *
        (((1 + (((pq.1 : ℕ) : ℝ) / ((pq.2 : ℕ) : ℝ)) ^ a : ℝ)) : ℂ) ^ (-ν)) =
      VerticalIntegral' (fun z => kMB a μ ν z * P z * P (L - z)) c := by
  have hi := mellinInv_kMB ha μ ν h1 h2 (t := 1) zero_lt_one
  have hf := fun t ht => (mellinInv_kMB ha μ ν h1 h2 (t := t) ht).2
  obtain ⟨hS, _, hI⟩ := tsum_eq_verticalIntegral'_of_mellin primeWeight_one hc1 hc2 hi.1 hf
  simpa only [ofReal_one, one_mul, primeSum_one, ← mul_assoc] using And.intro hS hI

end GoldbachBoundaries.Paper2.M4b
