import PrimePairNB.HInf.Defs

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Function
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- Translating an arc back to the graph preserves both its point and its velocity. -/
lemma graph_arc_point {κ : ℝ} (Γ : SlantGraph κ) (a : ℂ) (h : ℝ) :
    a + (((Γ.ξ (h + hgt κ a) - absc κ a : ℝ) : ℂ) + (h : ℂ) * I) * slantDir κ =
      Γ.pt (h + hgt κ a) := by
  have hw := ThmA.slantDir_ne_zero κ
  have ha : ((absc κ a : ℂ) + (hgt κ a : ℂ) * I) * slantDir κ = a := by
    rw [absc, hgt, Complex.re_add_im, div_mul_cancel₀ _ hw]
  simp only [SlantGraph.pt, Complex.ofReal_sub, Complex.ofReal_add]
  linear_combination -ha

lemma graph_arc_integral {κ : ℝ} (Γ : SlantGraph κ) (a : ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (f : ℂ → ℂ) :
    arcInt r₀ (fun h => Γ.ξ (h + hgt κ a) - absc κ a)
      (fun t => slantDir κ * f (a + t * slantDir κ)) =
      (1 / (2 * (Real.pi : ℂ) * I)) *
        ∫ h in Ioo (hgt κ a - r₀) (hgt κ a + r₀),
          f (Γ.pt h) * (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)) := by
  unfold arcInt
  congr 1
  have he : (fun h => slantDir κ *
      f (a + (((Γ.ξ (h + hgt κ a) - absc κ a : ℝ) : ℂ) + (h : ℂ) * I) * slantDir κ) *
        (((deriv (fun h => Γ.ξ (h + hgt κ a) - absc κ a) h : ℝ) : ℂ) + I)) =
      (fun h => f (Γ.pt (h + hgt κ a)) *
        (slantDir κ * (((deriv Γ.ξ (h + hgt κ a) : ℝ) : ℂ) + I))) := by
    funext h
    rw [graph_arc_point, deriv_sub_const, deriv_comp_add_const]
    ring
  rw [he]
  rw [intervalIntegral.integral_comp_add_right (f := fun h => f (Γ.pt h) *
    (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) (hgt κ a)]
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  congr 2 <;> ring

/-- Splitting a graph integral into the outer part and the arcs, in `t = (z - a) / slantDir κ`: on a band
`Γ.pt (h + h(a)) = a + slantDir κ · (ξ_a(h) + ih)` with `ξ_a(h) = Γ.ξ(h + h(a)) - absc a`. -/
theorem graphInt_eq_outer_add_arcs {κ : ℝ} (Γ : SlantGraph κ) {x : ℂ} (hfin : (collide x).Finite) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hdisj : ∀ a ∈ collide x, ∀ a' ∈ collide x, a ≠ a' → 2 * r₀ < |hgt κ a - hgt κ a'|) {f : ℂ → ℂ}
    (hf : Integrable fun h : ℝ => f (Γ.pt h) * (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) :
    graphInt Γ f =
      (1 / (2 * (Real.pi : ℂ) * I)) * (∫ h in outerHeights κ x r₀,
          f (Γ.pt h) * (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) +
        ∑ᶠ a ∈ collide x, arcInt r₀ (fun h => Γ.ξ (h + hgt κ a) - absc κ a)
          (fun t => slantDir κ * f (a + t * slantDir κ)) := by
  classical
  let B (a : ℂ) := Ioo (hgt κ a - r₀) (hgt κ a + r₀)
  have hc : (outerHeights κ x r₀)ᶜ = ⋃ a ∈ hfin.toFinset, B a := by
    ext h
    simp only [outerHeights, mem_compl_iff, mem_setOf_eq, not_forall, not_le,
      mem_iUnion, Set.Finite.mem_toFinset, B, mem_Ioo]
    constructor
    · rintro ⟨a, ha, hh⟩
      exact ⟨a, ha, by have := abs_lt.mp hh; constructor <;> linarith⟩
    · rintro ⟨a, ha, hh⟩
      exact ⟨a, ha, abs_lt.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩⟩
  have hm : MeasurableSet (outerHeights κ x r₀) := by
    have : IsClosed (outerHeights κ x r₀) := by
      simp only [outerHeights, setOf_forall]
      exact isClosed_biInter fun a ha => isClosed_le continuous_const (by fun_prop)
    exact this.measurableSet
  have hd : Set.Pairwise (↑hfin.toFinset) (Disjoint on B) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro h hha hhb
    have hs := hdisj a (hfin.mem_toFinset.mp ha) b (hfin.mem_toFinset.mp hb) hab
    have ht := abs_sub_le (hgt κ a) h (hgt κ b)
    have ha' : |h - hgt κ a| < r₀ := abs_lt.mpr ⟨by linarith [hha.1], by linarith [hha.2]⟩
    have hb' : |h - hgt κ b| < r₀ := abs_lt.mpr ⟨by linarith [hhb.1], by linarith [hhb.2]⟩
    rw [abs_sub_comm (hgt κ a) h] at ht
    linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp_rw [graph_arc_integral Γ _ hr₀ f]
  rw [← Finset.mul_sum, ← mul_add, graphInt, ← integral_add_compl hm hf, hc]
  congr 2
  exact integral_biUnion_finset hfin.toFinset (fun _ _ => measurableSet_Ioo) hd
    (fun _ _ => hf.integrableOn)

end GoldbachBoundaries.HInf.Fill

