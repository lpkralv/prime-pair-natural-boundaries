import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.G13_Continuation

/-!
# The jump identity, every branch, and tools for the boundary

The jump corollary, the branch proposition, and the general facts used in the boundary theorem for `G`, the domain corollary,
the every-path statement. Everything except the last section is stated for an arbitrary `Gn` with
`IsPrincipalSheet κ Gn` (no integrals, no RH).

The lemmas `jump_of_access`, `isBranch_uniform_cut`, `exists_path_into`,
`exists_component_reaching_line`, `no_analytic_across_log` are proved in `Fill/<name>.lean`;
`isBranch_uniform_omega`, `isBranch_uniform` and `isBranch_of_admissible` are in `Assembly.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

/-- Modify a meromorphic function at one point so that it has a given analytic germ there. -/
theorem exists_meromorphic_update {f g : ℂ → ℂ} {U : Set ℂ} {s₁ : ℂ} (hf : MeromorphicOn f U)
    (hfg : f =ᶠ[𝓝[≠] s₁] g) :
    ∃ f' : ℂ → ℂ, MeromorphicOn f' U ∧ f' =ᶠ[𝓝 s₁] g ∧
      ∀ᶠ z in codiscreteWithin U, AnalyticAt ℂ f' z := by
  classical
  set f' : ℂ → ℂ := Function.update f s₁ (g s₁) with hf'def
  have hff' : ∀ z, f =ᶠ[𝓝[≠] z] f' := by
    intro z
    by_cases hz : z = s₁
    · subst hz
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hf'def, Function.update_of_ne hw]
    · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hz)] with w hw
      rw [hf'def, Function.update_of_ne hw]
  have hm : MeromorphicOn f' U := fun z hz => (hf z hz).congr (hff' z)
  refine ⟨f', hm, ?_, hm.eventually_codiscreteWithin_analyticAt⟩
  have h1 : f' =ᶠ[𝓝[≠] s₁] g := (hff' s₁).symm.trans hfg
  rw [← nhdsNE_sup_pure]
  exact Filter.eventually_sup.mpr ⟨h1, Filter.eventually_pure.mpr (by simp [hf'def])⟩

theorem isBranch_congr {κ : ℝ} {Gn : ℂ → ℂ} {p : ℂ} {f g : ℂ → ℂ} (h : IsBranch κ Gn p f)
    (hfg : f =ᶠ[𝓝 p] g) : IsBranch κ Gn p g := by
  refine ⟨h.1.congr hfg, ?_⟩
  filter_upwards [h.2, hfg.eventuallyEq_nhds] with q hq hq' hqΩ
  obtain ⟨m, hm, hfm⟩ := hq hqΩ
  exact ⟨m, hm, hq'.symm.trans hfm⟩

/-- Copy of `Statements.lean`'s `G_differentiableOn`. -/
theorem G_differentiableOn {a : ℝ} (ha : 2 < a) : DifferentiableOn ℂ G (halfPlane a) := by
  set b : ℝ := a / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  have hS : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b)) :=
    (Real.summable_nat_rpow.2 (by linarith)).subtype _
  have hnn : 0 ≤ (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b)) :=
    fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS2 := hS.mul_of_nonneg hS hnn hnn
  refine differentiableOn_tsum_of_summable_norm hS2 ?_ (isOpen_halfPlane a) ?_
  · intro pq w _
    have hpos : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ≠ 0 := by
      have := pq.1.2.pos; exact_mod_cast (by omega)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hpos)).differentiableWithinAt
  · intro pq w hw
    have hp : 0 < (pq.1 : ℕ) := pq.1.2.pos
    have hq : 0 < (pq.2 : ℕ) := pq.2.2.pos
    rw [norm_natCast_cpow_of_pos (by omega)]
    simp only [neg_re]
    have hw' : a < w.re := hw
    set n : ℝ := (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) with hn
    have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast (by omega)
    have hpn : ((pq.1 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega)
    have hqn : ((pq.2 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega)
    calc n ^ (-w.re) ≤ n ^ (-a) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n ^ (-b) * n ^ (-b) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; rw [hb]; ring
      _ ≤ ((pq.1 : ℕ) : ℝ) ^ (-b) * ((pq.2 : ℕ) : ℝ) ^ (-b) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp) hpn (by linarith)
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hq) hqn (by linarith)
          · exact Real.rpow_nonneg (by linarith) _
          · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem G_analyticAt {s : ℂ} (hs : 2 < s.re) : AnalyticAt ℂ G s := by
  have ha : 2 < (s.re + 2) / 2 := by linarith
  refine (G_differentiableOn ha).analyticAt ((isOpen_halfPlane _).mem_nhds ?_)
  show (s.re + 2) / 2 < s.re
  linarith

/-- `G` itself is a branch at every point of `σ > 2`. -/
theorem isBranch_G {κ : ℝ} {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn) {p : ℂ} (hp : 2 < p.re) :
    IsBranch κ Gn p G := by
  refine ⟨G_analyticAt hp, ?_⟩
  filter_upwards [(isOpen_halfPlane 2).mem_nhds hp] with q hq _
  refine ⟨0, zero_mem _, ?_⟩
  filter_upwards [(isOpen_halfPlane 2).mem_nhds hq] with s hs
  simp [hP.eq_G hs]

theorem admissible_mem {g : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁) :
    s₁ ∈ HH \ catalogue := by
  obtain ⟨γ, hγ, -, h1, -⟩ := hg
  rw [← h1]; exact hγ 1

theorem admissible_analyticAt {g : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁) :
    AnalyticAt ℂ g s₁ := by
  obtain ⟨γ, -, -, h1, f, hf, -, hg1⟩ := hg
  rw [← h1]; exact (hf.analyticAt 1).congr hg1.symm

/-- A catalogue point in every disc centred on the line (from the density lemma). -/
theorem exists_catalogue_mem_ball (y : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ α ∈ catalogue, α ∈ ball (1 + (y : ℂ) * I) r := by
  obtain ⟨⟨n, ρ⟩, hn, hρ, hlt⟩ := (lem_density_proof y hr).nonempty
  refine ⟨1 + ρ / (n : ℂ), Or.inr ⟨n, hn.one_lt.le, hn.prime.squarefree, ρ, hρ, rfl⟩, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have : 1 + ρ / (n : ℂ) - (1 + (y : ℂ) * I) = ρ / (n : ℂ) - (y : ℂ) * I := by ring
  rw [this]; exact hlt

end GoldbachBoundaries.ThmA
