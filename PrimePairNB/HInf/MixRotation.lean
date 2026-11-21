import PrimePairNB.HInf.MixJumpLine
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- **Rotation.** If `v₁ ∈ Ω_κ ∩ Ω_κ'`, `κ < κ'`, then as germs at `v₁`, `D^{κ'} - D^κ = ∑ M_x` over
catalogue points in the open sector, a finite sum. -/
theorem rotation (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) {v₁ : ℂ} {κ κ' : ℝ} (hκ : κ < κ') (h₁ : v₁ ∈ Om κ ⊤) (h₂ : v₁ ∈ Om κ' ⊤) :
    (sector v₁ κ κ' ∩ Xcat).Finite ∧
      DthMix κ' =ᶠ[𝓝 v₁] fun v => DthMix κ v + sumMcMix (sector v₁ κ κ') v := by
  classical
  have hvV : v₁ ∈ VInf ⊤ := h₁.1
  have hvX : v₁ ∉ Pinch := not_mem_Pinch_of_mem_Om h₁
  have hfin (a b : ℝ) := sector_inter_Xcat_finite hZ1 hvV a b
  refine ⟨hfin κ κ', ?_⟩
  have aux : ∀ n : ℕ, ∀ {a b : ℝ}, a < b → v₁ ∈ Om a ⊤ → v₁ ∈ Om b ⊤ →
      (sector v₁ a b ∩ Xcat).ncard = n →
      DthMix b =ᶠ[𝓝 v₁] fun v => DthMix a v + sumMcMix (sector v₁ a b) v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hab ha hb hn
      let F : Set ℂ := sector v₁ a b ∩ Xcat
      have hF : F.Finite := hfin a b
      by_cases hne : F.Nonempty
      · obtain ⟨x, hx, hmin⟩ := Set.exists_min_image F (lineSlope v₁) hF hne
        let c : ℝ := lineSlope v₁ x
        have hxc := (mem_sector_iff_lineSlope.mp hx.1).2
        have hac : a < c := hxc.1
        have hcb : c < b := hxc.2
        obtain ⟨_, δ, hδ, hj⟩ := jump_line hZ1 hZ2 hZ3 hK hvV hvX c
        let ε : ℝ := min δ (min (c - a) (b - c)) / 2
        have hε : 0 < ε := half_pos (lt_min hδ (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb)))
        have hεd : ε < δ := by
          have h1 := min_le_left δ (min (c - a) (b - c))
          dsimp [ε]
          linarith
        have hεa : ε < c - a := by
          have h1 := (min_le_right δ (min (c - a) (b - c))).trans (min_le_left _ _)
          dsimp [ε] at *
          linarith
        have hεb : ε < b - c := by
          have h1 := (min_le_right δ (min (c - a) (b - c))).trans (min_le_right _ _)
          dsimp [ε] at *
          linarith
        let m : ℝ := c - ε
        let p : ℝ := c + ε
        have ham : a < m := by dsimp [m]; linarith
        have hmc : m < c := by dsimp [m]; linarith
        have hcp : c < p := by dsimp [p]; linarith
        have hpb : p < b := by dsimp [p]; linarith
        have hm : m ∈ Ioo (c - δ) c := by dsimp [m]; constructor <;> linarith
        have hp : p ∈ Ioo c (c + δ) := by dsimp [p]; constructor <;> linarith
        have hjmp := hj m hm p hp
        have hleft : DthMix m =ᶠ[𝓝 v₁] DthMix a := by
          apply germ_const hZ1 hZ2 hZ3 hK ham.le
          intro σ hσ
          by_cases hσa : σ = a
          · simpa [hσa] using ha
          apply (mem_Om_iff_no_ray hvV hvX σ).mpr
          intro y hy hyr
          have hys := mem_rayE_iff_lineSlope.mp hyr
          have hyF : y ∈ F := ⟨mem_sector_iff_lineSlope.mpr
            ⟨hys.1, by rw [hys.2]; exact ⟨lt_of_le_of_ne hσ.1 (Ne.symm hσa), by linarith [hσ.2]⟩⟩, hy⟩
          have hh := hmin y hyF
          rw [hys.2] at hh
          change c ≤ σ at hh
          linarith [hσ.2]
        let F' : Set ℂ := sector v₁ p b ∩ Xcat
        have hF' : F'.Finite := hfin p b
        have hsub : F' ⊆ F := by
          intro y hy
          have hys := mem_sector_iff_lineSlope.mp hy.1
          exact ⟨mem_sector_iff_lineSlope.mpr ⟨hys.1, by
            constructor <;> linarith [hys.2.1, hys.2.2]⟩, hy.2⟩
        have hxn : x ∉ F' := by
          intro hh
          have h := (mem_sector_iff_lineSlope.mp hh.1).2.1
          change p < c at h
          linarith
        have hproper : F' ⊂ F := ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hxn (by rw [he]; exact hx)⟩
        have hlt : F'.ncard < n := by
          rw [← hn]
          exact Set.ncard_lt_ncard hproper hF
        have hright := ih F'.ncard hlt hpb hjmp.2.1 hb rfl
        let L : Set ℂ := rayE c v₁ ∩ Xcat
        have hL : L.Finite := rayE_inter_Xcat_finite hZ1 hvV c
        have hpartition : F = L ∪ F' := by
          ext y
          constructor
          · intro hy
            have hys := mem_sector_iff_lineSlope.mp hy.1
            by_cases he : lineSlope v₁ y = c
            · exact Or.inl ⟨mem_rayE_iff_lineSlope.mpr ⟨hys.1, he⟩, hy.2⟩
            · have hcy : c < lineSlope v₁ y := lt_of_le_of_ne (hmin y hy) (Ne.symm he)
              have hpy : p < lineSlope v₁ y := by
                by_contra hnpy
                have hym : v₁ ∈ Om (lineSlope v₁ y) ⊤ :=
                  (hj m hm (lineSlope v₁ y) ⟨hcy, by linarith [le_of_not_gt hnpy, hp.2]⟩).2.1
                exact ((mem_Om_iff_no_ray hvV hvX _).mp hym y hy.2)
                  (mem_rayE_iff_lineSlope.mpr ⟨hys.1, rfl⟩)
              exact Or.inr ⟨mem_sector_iff_lineSlope.mpr ⟨hys.1, hpy, hys.2.2⟩, hy.2⟩
          · rintro (hy | hy)
            · have hys := mem_rayE_iff_lineSlope.mp hy.1
              exact ⟨mem_sector_iff_lineSlope.mpr ⟨hys.1, by rw [hys.2]; exact ⟨hac, hcb⟩⟩, hy.2⟩
            · exact hsub hy
        have hdisj : Disjoint L F' := by
          apply Set.disjoint_left.mpr
          intro y hy hy'
          have he := (mem_rayE_iff_lineSlope.mp hy.1).2
          have hh := (mem_sector_iff_lineSlope.mp hy'.1).2.1
          rw [he] at hh
          linarith
        have hsum (v : ℂ) : sumMcMix (sector v₁ a b) v =
            sumMcMix (rayE c v₁) v + sumMcMix (sector v₁ p b) v := by
          change (∑ᶠ y ∈ F, McMix y v) = (∑ᶠ y ∈ L, McMix y v) + ∑ᶠ y ∈ F', McMix y v
          rw [hpartition]
          exact finsum_mem_union hdisj hL hF'
        filter_upwards [hright, hjmp.2.2, hleft] with v hvR hvJ hvL
        rw [hvR, hvJ, hvL, hsum]
        ring
      · have hempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hall : ∀ σ ∈ Icc a b, v₁ ∈ Om σ ⊤ := by
          intro σ hσ
          rcases eq_or_lt_of_le hσ.1 with he | he
          · simpa [← he] using ha
          rcases eq_or_lt_of_le hσ.2 with he' | he'
          · simpa [he'] using hb
          apply (mem_Om_iff_no_ray hvV hvX σ).mpr
          intro y hy hyr
          have hys := mem_rayE_iff_lineSlope.mp hyr
          have hyF : y ∈ F := ⟨mem_sector_iff_lineSlope.mpr ⟨hys.1, by rw [hys.2]; exact ⟨he, he'⟩⟩, hy⟩
          simpa [hempty] using hyF
        have hsame := germ_const hZ1 hZ2 hZ3 hK hab.le hall
        filter_upwards [hsame] with v hv
        have hz : sumMcMix (sector v₁ a b) v = 0 := by
          change (∑ᶠ y ∈ F, McMix y v) = 0
          simp [hempty]
        simpa [hz] using hv
  exact aux _ hκ h₁ h₂ rfl

end GoldbachBoundaries.HInf.MixProof
