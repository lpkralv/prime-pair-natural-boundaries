import PrimePairNB.HInf.Fill.absc_lt_iff_re_lt

/-! Proof of `isSeparating_eventually`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma continuous_hgt (κ : ℝ) : Continuous (hgt κ) := by
  unfold hgt; fun_prop

lemma continuous_absc (κ : ℝ) : Continuous (absc κ) := by
  unfold absc; fun_prop

/-- A graph separating for `v₁` separates for `v` near `v₁`. -/
theorem isSeparating_eventually (hZ1 : Z1) {κ : ℝ} {v₁ : ℂ} {Γ : SlantGraph κ} (hΓ : IsSeparating v₁ Γ) :
    ∀ᶠ v in 𝓝 v₁, IsSeparating v Γ := by
  obtain ⟨⟨ε₁, hε, hre⟩, ⟨hc1, hc2⟩, hleft, hright⟩ := hΓ
  set η : ℝ := (v₁.re - Binf - Γ.c) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set δ : ℝ := min (ε₁ / 2) η with hδ
  have hδpos : 0 < δ := lt_min (by positivity) hηpos
  have hδ1 : δ ≤ ε₁ / 2 := min_le_left _ _
  have hδ2 : δ ≤ η := min_le_right _ _
  set T' : ℝ := Γ.T + |hgt κ v₁| + 1 with hT'
  have hBf : (Fdelta η ∪ {b | b ∈ PoleSetQ ∧ ε₁ / 2 ≤ b.re ∧ |hgt κ b| ≤ T'}).Finite :=
    (M1.Fdelta_spec hZ1 η hηpos).1.union (finite_poleSetQ_height κ (by positivity) T')
  have ev1 : ∀ᶠ v : ℂ in 𝓝 v₁, v₁.re - δ < v.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by show v₁.re - δ < v₁.re; linarith)
  have ev2 : ∀ᶠ v : ℂ in 𝓝 v₁, |hgt κ v| < |hgt κ v₁| + 1 :=
    (isOpen_lt (continuous_hgt κ).abs continuous_const).mem_nhds (by show |hgt κ v₁| < |hgt κ v₁| + 1; linarith)
  have ev3 : ∀ᶠ v : ℂ in 𝓝 v₁, ∀ b ∈ Fdelta η ∪ {b | b ∈ PoleSetQ ∧ ε₁ / 2 ≤ b.re ∧ |hgt κ b| ≤ T'},
      Γ.ξ (hgt κ (v - b)) < absc κ (v - b) := by
    refine (Filter.eventually_all_finite hBf).2 fun b hb => ?_
    have hbP : b ∈ PoleSetQ := by
      rcases hb with hb | hb
      · exact hb.1
      · exact hb.1
    have c1 : Continuous fun v : ℂ => Γ.ξ (hgt κ (v - b)) :=
      Γ.cont.comp ((continuous_hgt κ).comp (continuous_id.sub continuous_const))
    have c2 : Continuous fun v : ℂ => absc κ (v - b) :=
      (continuous_absc κ).comp (continuous_id.sub continuous_const)
    exact (isOpen_lt c1 c2).mem_nhds (hright b hbP)
  filter_upwards [ev1, ev2, ev3] with v hv1 hv2 hv3
  refine ⟨⟨ε₁ / 2, by positivity, fun h => ?_⟩, ⟨hc1, ?_⟩, hleft, fun b hb => ?_⟩
  · obtain ⟨a0, a1⟩ := hre h
    constructor <;> linarith
  · show Γ.c < v.re - Binf
    rw [hη] at hδ2
    linarith
  · by_cases hbf : b ∈ Fdelta η ∪ {b | b ∈ PoleSetQ ∧ ε₁ / 2 ≤ b.re ∧ |hgt κ b| ≤ T'}
    · exact hv3 b hbf
    · have hb1 : b ∉ Fdelta η := fun h => hbf (Or.inl h)
      have hb2 : ¬ (b ∈ PoleSetQ ∧ ε₁ / 2 ≤ b.re ∧ |hgt κ b| ≤ T') := fun h => hbf (Or.inr h)
      have hbF : b.re ≤ Binf + η := by
        by_contra hc
        exact hb1 ⟨hb, not_le.mp hc⟩
      have hr := re_eq_absc κ (v - b)
      have hre' : (v - b).re = v.re - b.re := by simp
      by_cases hsmall : b.re < ε₁ / 2
      · have hp := (hre (hgt κ (v - b))).2
        rw [pt_re] at hp
        linarith
      · have hbig : T' < |hgt κ b| := by
          by_contra hc
          exact hb2 ⟨hb, not_lt.mp hsmall, not_lt.mp hc⟩
        have hT : Γ.T ≤ |hgt κ (v - b)| := by
          rw [hgt_sub, abs_sub_comm]
          have := abs_sub_abs_le_abs_sub (hgt κ b) (hgt κ v)
          rw [hT'] at hbig
          linarith
        have ht := Γ.tail _ hT
        rw [ht]
        rw [hη] at hbF hδ2
        linarith

end GoldbachBoundaries.HInf.Fill

