import PrimePairNB.HInf.Defs

/-! Proofs of `re_le_two_of_mem_pinch`, `VInf_eq_of_Hinf`, `mem_Om_of_two_lt`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `Re a ≤ 1` on `Σ` gives `Re x ≤ 2` on `Σ + Σ`: every cut lies in `Re v ≤ 2`. -/
theorem re_le_two_of_mem_pinch {x : ℂ} (hx : x ∈ Pinch) : x.re ≤ 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have h1 := (GoldbachBoundaries.Paper2.M1.poleSetQ_re_bounds ha).2.1
  have h2 := (GoldbachBoundaries.Paper2.M1.poleSetQ_re_bounds hb).2.1
  simp only [Complex.add_re]
  linarith

/-- Under `(H_∞)` and (Z1), `𝒱_∞ = 𝒱`: the domain reaches the line.  -/
theorem VInf_eq_of_Hinf (hZ1 : Z1) (hH : Hinf) (top : EReal) : VInf top = Vt top := by
  have hB := GoldbachBoundaries.Paper2.M2.Binf_eq_half_of_Hinf hZ1 hH
  ext v
  simp only [VInf, Vt, mem_setOf_eq, hB]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by linarith [h.1]⟩

/-- Binf is at most `1`. -/
theorem Binf_le_one : Binf ≤ 1 :=
  (GoldbachBoundaries.Paper2.M1.Binf_le_Bsup_le_one.1).trans
    GoldbachBoundaries.Paper2.M1.Binf_le_Bsup_le_one.2

/-- The strip `2 < Re v` of `𝒱` lies in every `Ω_θ`, since `Re x ≤ 2` and `2B_∞ ≤ 2`. -/
theorem mem_Om_of_two_lt (hZ1 : Z1) {κ : ℝ} {top : EReal} {v : ℂ} (hv : v ∈ Vt top) (h2 : 2 < v.re) :
    v ∈ Om κ top := by
  refine ⟨⟨hv, by linarith [Binf_le_one]⟩, ?_⟩
  simp only [mem_iUnion, not_exists]
  rintro x hx ⟨t, ht, hvx⟩
  have := re_le_two_of_mem_pinch hx
  have hre : v.re = x.re - t := by
    rw [hvx]; simp [slantDir]
  linarith

end GoldbachBoundaries.HInf.Fill

