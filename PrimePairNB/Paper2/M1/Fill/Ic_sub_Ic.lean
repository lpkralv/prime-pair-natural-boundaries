import PrimePairNB.Paper2.M1.Fill.E1Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.half_le_Binf

/-!
# `Ic_sub_Ic`: the shift between two admissible lines

Between the lines `c' < c` the poles of `g_s(w) = K_s(w) Q(w) Q(s - w)` are the left points `a ∈ F_δ` with
`c' < Re a < c` (residue `R_a K_s(a) Q(s - a)`) and the right points `s - b`, `b ∈ F_δ`, `c' < σ - Re b < c`
(residue `-R_b K_s(b) Q(s - b)`). The two sets are disjoint because `s ∉ Π`; no pole lies on either line by
admissibility and the two region conditions.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Shift between two admissible lines** (Z1, Z2, Z3). For admissible
`c' < c` (same `δ`) and `s` in both regions with `s ∉ Π`: the poles of `w ↦ K_s(w) Q(w) Q(s - w)` in the strip
`c' < Re w < c` are the left points `a ∈ F_δ` with `c' < Re a < c` (residue `R_a K_s(a) Q(s - a)`) and the right points
`s - b`, `b ∈ F_δ` with `c' < σ - Re b < c` (residue `-R_b K_s(b) Q(s - b)`, by `K_s(s - w) = K_s(w)`); they are
distinct because `s ∉ Π`, and none lies on either line. Uses: `verticalIntegral'_eq_add_sum_of_simplePoles`,
`E1_norm_gs_le_far`, `hasResidue_Qcont_Rcoef`, `meromorphicOrderAt_Qcont_ge`, `KerS_sub_symm`, `Fdelta_spec`. -/
theorem Ic_sub_Ic (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c c' : ℝ} (h : AdmC δ c) (h' : AdmC δ c')
    (hcc : c' < c) {s : ℂ} (hs : s ∈ RegC δ c) (hs' : s ∈ RegC δ c') (hsP : s ∉ Pinch) :
    IcQ Qcont c s - IcQ Qcont c' s =
      ∑ᶠ a ∈ {a | a ∈ Fdelta δ ∧ c' < a.re ∧ a.re < c}, Rcoef a * KerS s a * Qcont (s - a) -
        ∑ᶠ b ∈ {b | b ∈ Fdelta δ ∧ c' < s.re - b.re ∧ s.re - b.re < c},
          Rcoef b * KerS s b * Qcont (s - b) := by
  have hδ : 0 < δ := h.1
  have hB := half_le_Binf hZ1
  have hc'1 : Binf + 2 * δ < c' := h'.2.2.1
  have hσ : c + Binf + 2 * δ < s.re := hs.1
  have hF := (Fdelta_spec hZ1 δ hδ).1
  set X : ℂ → ℂ := fun a => Rcoef a * KerS s a * Qcont (s - a) with hX
  set L : Finset ℂ := hF.toFinset.filter (fun a => c' < a.re ∧ a.re < c) with hL
  set RB : Finset ℂ := hF.toFinset.filter (fun b => c' < s.re - b.re ∧ s.re - b.re < c) with hRB
  set R : Finset ℂ := RB.image (fun b => s - b) with hR
  have hmemL : ∀ p, p ∈ L ↔ p ∈ Fdelta δ ∧ c' < p.re ∧ p.re < c := by intro p; simp [hL]
  have hmemRB : ∀ b, b ∈ RB ↔ b ∈ Fdelta δ ∧ c' < s.re - b.re ∧ s.re - b.re < c := by
    intro b; simp [hRB]
  have hmemR : ∀ p, p ∈ R ↔ s - p ∈ RB := by
    intro p
    simp only [hR, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩; rwa [sub_sub_cancel]
    · intro hp; exact ⟨s - p, hp, sub_sub_cancel s p⟩
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p hpL hpR
    have h1 := ((hmemL p).1 hpL).1.1
    have h2 := ((hmemRB _).1 ((hmemR p).1 hpR)).1.1
    exact hsP ⟨p, h1, s - p, h2, by ring⟩
  set A : ℂ → ℂ := fun p => if p ∈ L then X p else -(Rcoef (s - p) * KerS s (s - p) * Qcont p)
    with hA
  have hshift := E1_shift hZ1 hZ2 hZ3 hδ (c₁ := c') (c₂ := c) hc'1.le hcc.le (s := s) hσ.le (L ∪ R) A
    (by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨((hmemL p).1 hp).2.1, ((hmemL p).1 hp).2.2⟩
      · obtain ⟨-, h1, h2⟩ := (hmemRB _).1 ((hmemR p).1 hp)
        simp only [sub_re, sub_sub_cancel] at h1 h2
        exact ⟨h1, h2⟩)
    (by
      rintro w ⟨hw, hwS⟩
      have hwre := (mem_reProdIm.mp hw).1
      have hwS' : w ∉ L ∧ w ∉ R := by
        simpa only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] using hwS
      refine (E1_differentiableAt_g ?_ ?_ ?_ ?_).differentiableWithinAt
      · linarith [hwre.1]
      · simp only [sub_re]; linarith [hwre.2]
      · intro hwP
        have hwF : w ∈ Fdelta δ := ⟨hwP, by linarith [hwre.1]⟩
        have h1 : w.re ≠ c := fun e => h.2.2.2.2 w hwF e.symm
        have h2 : w.re ≠ c' := fun e => h'.2.2.2.2 w hwF e.symm
        exact hwS'.1 ((hmemL w).2 ⟨hwF, lt_of_le_of_ne hwre.1 h2.symm, lt_of_le_of_ne hwre.2 h1⟩)
      · intro hP
        have hbF : s - w ∈ Fdelta δ := ⟨hP, by simp only [sub_re]; linarith [hwre.2]⟩
        have e1 := hs.2 _ hbF
        have e2 := hs'.2 _ hbF
        simp only [sub_re] at e1 e2
        have h1 : w.re ≠ c := fun e => e1 (by rw [e]; ring)
        have h2 : w.re ≠ c' := fun e => e2 (by rw [e]; ring)
        refine hwS'.2 ((hmemR w).2 ((hmemRB _).2 ⟨hbF, ?_, ?_⟩))
        · simp only [sub_re, sub_sub_cancel]; exact lt_of_le_of_ne hwre.1 h2.symm
        · simp only [sub_re, sub_sub_cancel]; exact lt_of_le_of_ne hwre.2 h1)
    (by
      intro p hp
      by_cases hpL : p ∈ L
      · have hpA : A p = X p := by simp only [hA, hpL, ↓reduceIte]
        rw [hpA]
        obtain ⟨hpF, -, hpc⟩ := (hmemL p).1 hpL
        exact E1_pole_left hpF.1 (by simp only [sub_re]; linarith)
          fun hP => hsP ⟨p, hpF.1, s - p, hP, by ring⟩
      · have hpR : p ∈ R := by
          rcases Finset.mem_union.mp hp with h1 | h1
          · exact absurd h1 hpL
          · exact h1
        have hpA : A p = -(Rcoef (s - p) * KerS s (s - p) * Qcont p) := by
          simp only [hA, hpL, ↓reduceIte]
        rw [hpA]
        obtain ⟨hbF, h1, -⟩ := (hmemRB _).1 ((hmemR p).1 hpR)
        simp only [sub_re, sub_sub_cancel] at h1
        exact E1_pole_right hbF.1 (by linarith)
          fun hP => hsP ⟨p, hP, s - p, hbF.1, by ring⟩)
  -- identify the finite sums
  have hsetL : ({a | a ∈ Fdelta δ ∧ c' < a.re ∧ a.re < c} : Set ℂ) = (L : Set ℂ) := by
    ext a; simp only [Set.mem_ofPred_eq, Finset.mem_coe, hmemL]
  have hsetR : ({b | b ∈ Fdelta δ ∧ c' < s.re - b.re ∧ s.re - b.re < c} : Set ℂ) = (RB : Set ℂ) := by
    ext b; simp only [Set.mem_ofPred_eq, Finset.mem_coe, hmemRB]
  rw [hsetL, hsetR, finsum_mem_coe_finset, finsum_mem_coe_finset, hshift,
    Finset.sum_union hdisj, hR, Finset.sum_image (fun b₁ _ b₂ _ e => sub_right_injective e)]
  have hLsum : ∑ p ∈ L, A p = ∑ p ∈ L, X p :=
    Finset.sum_congr rfl fun p hp => by simp only [hA, hp, ↓reduceIte]
  have hRsum : ∑ b ∈ RB, A (s - b) = -∑ b ∈ RB, X b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hnot : s - b ∉ L := fun hL' =>
      Finset.disjoint_left.mp hdisj hL' ((hmemR _).2 (by rwa [sub_sub_cancel]))
    simp only [hA, hnot, ↓reduceIte, sub_sub_cancel, hX]
  rw [hLsum, hRsum]
  ring

end GoldbachBoundaries.Paper2.M1
