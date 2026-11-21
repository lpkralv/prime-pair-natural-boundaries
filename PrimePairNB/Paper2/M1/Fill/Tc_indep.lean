import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.Ic_sub_Ic
import PrimePairNB.Paper2.M1.Fill.Tc_mono_delta

/-!
# `Tc_indep`

Reduce to the common `δ'' = min δ δ'` (`Tc_mono_delta`), order the lines, and apply `Ic_sub_Ic`: with no
equalities (admissibility, regions), `ν_c(a) - ν_{c'}(a) = -[c' < Re a < c] + [c' < σ - Re a < c]`, which cancels the
two residue sums.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The indicator identity behind `Tc_indep`, at one point `a` (no equalities among the four real numbers). -/
lemma E1_nu_sub {e e' σ x : ℝ} (hlt : e' < e) (h1 : x ≠ e) (h3 : σ - x ≠ e') (X : ℂ) (s : ℂ) (a : ℂ)
    (hσ : s.re = σ) (hx : a.re = x) :
    nu e a s * X =
      nu e' a s * X - (if e' < x ∧ x < e then X else 0) + (if e' < σ - x ∧ σ - x < e then X else 0) := by
  simp only [nu, iverson, hσ, hx, ite_and]
  have h1' := h1
  have h3' := h3
  split_ifs <;> first | ring1 | (exfalso; linarith) | (exfalso; exact h1' (by linarith)) |
    (exfalso; exact h3' (by linarith))

/-- Two admissible lines `e' < e` with the same `δ`: `𝒯_e(s) = 𝒯_{e'}(s)` off `Π`. -/
lemma E1_Tc_eq_of_lt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {d e e' : ℝ} (he : AdmC d e) (he' : AdmC d e')
    (hlt : e' < e) {s : ℂ} (hs : s ∈ RegC d e) (hs' : s ∈ RegC d e') (hsP : s ∉ Pinch) :
    Tc d e s = Tc d e' s := by
  have hF := (Fdelta_spec hZ1 d he.1).1
  have hI := Ic_sub_Ic hZ1 hZ2 hZ3 he he' hlt hs hs' hsP
  set X : ℂ → ℂ := fun a => Rcoef a * KerS s a * Qcont (s - a) with hX
  have hsetL : ({a | a ∈ Fdelta d ∧ e' < a.re ∧ a.re < e} : Set ℂ) =
      ((hF.toFinset.filter fun a => e' < a.re ∧ a.re < e : Finset ℂ) : Set ℂ) := by
    ext a; simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  have hsetR : ({b | b ∈ Fdelta d ∧ e' < s.re - b.re ∧ s.re - b.re < e} : Set ℂ) =
      ((hF.toFinset.filter fun b => e' < s.re - b.re ∧ s.re - b.re < e : Finset ℂ) : Set ℂ) := by
    ext a; simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  rw [hsetL, hsetR, finsum_mem_coe_finset, finsum_mem_coe_finset, Finset.sum_filter,
    Finset.sum_filter] at hI
  show IcQ Qcont e s + _ = IcQ Qcont e' s + _
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ hF]
  have hpt : ∀ a ∈ hF.toFinset, nu e a s * Rcoef a * KerS s a * Qcont (s - a) =
      nu e' a s * Rcoef a * KerS s a * Qcont (s - a) -
        (if e' < a.re ∧ a.re < e then X a else 0) +
        (if e' < s.re - a.re ∧ s.re - a.re < e then X a else 0) := by
    intro a ha
    have haF := hF.mem_toFinset.mp ha
    have h1 : a.re ≠ e := fun h => he.2.2.2.2 a haF h.symm
    have h3 : s.re - a.re ≠ e' := fun h => hs'.2 a haF (by rw [← h]; ring)
    have := E1_nu_sub hlt h1 h3 (X a) s a rfl rfl
    simp only [hX] at this ⊢
    linear_combination this
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hI

/-- **`𝒯_c(s)` does not depend on the admissible `(δ, c)`** off `Π` (Z1, Z2, Z3). Reduce to a common `δ` with
`Tc_mono_delta`, order the lines, and apply `Ic_sub_Ic`: with no equalities (admissibility, regions),
`ν_c(a) - ν_{c'}(a) = -[c' < Re a < c] + [c' < σ - Re a < c]`, which cancels the two residue sums.
Uses: `Tc_mono_delta`, `Ic_sub_Ic`, `Fdelta_spec`. -/
theorem Tc_indep (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c δ' c' : ℝ} (h : AdmC δ c) (h' : AdmC δ' c')
    {s : ℂ} (hs : s ∈ RegC δ c) (hs' : s ∈ RegC δ' c') (hsP : s ∉ Pinch) : Tc δ c s = Tc δ' c' s := by
  have hd : 0 < min δ δ' := lt_min h.1 h'.1
  obtain ⟨hA1, hR1⟩ := Tc_mono_delta hZ1 h hd (min_le_left _ _)
  obtain ⟨hA2, hR2⟩ := Tc_mono_delta hZ1 h' hd (min_le_right _ _)
  obtain ⟨hs1, he1⟩ := hR1 s hs
  obtain ⟨hs2, he2⟩ := hR2 s hs'
  rw [← he1, ← he2]
  rcases lt_trichotomy c' c with hlt | heq | hgt
  · exact E1_Tc_eq_of_lt hZ1 hZ2 hZ3 hA1 hA2 hlt hs1 hs2 hsP
  · rw [heq]
  · exact (E1_Tc_eq_of_lt hZ1 hZ2 hZ3 hA2 hA1 hgt hs2 hs1 hsP).symm

/-! Consequences of this file's lemma. -/

/-- Off `Π`, `Tcont` is the `𝒯_c` of every admissible `(δ, c)` whose region contains the point. -/
lemma Tcont_eq_Tc (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) {s : ℂ} (hs : s ∈ RegC δ c)
    (hP : s ∉ Pinch) : Tcont s = Tc δ c s := by
  have hex : Binf < 1 ∧ ∃ p : ℝ × ℝ, AdmC p.1 p.2 ∧ s ∈ RegC p.1 p.2 := ⟨h.Binf_lt_one, ⟨(δ, c), h, hs⟩⟩
  rw [Tcont_eq_choose hex]
  exact Tc_indep hZ1 hZ2 hZ3 hex.2.choose_spec.1 h hex.2.choose_spec.2 hs hP

end GoldbachBoundaries.Paper2.M1
