import PrimePairNB.HInf.MixJumpTransport
import PrimePairNB.HInf.MixMonodromy
import PrimePairNB.HInf.Fill.jump_line
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- Every nearby noncentral slope remains clear along the original east ray,
until a catalogue point itself is reached. -/
private lemma east_punctured_mem  {v : ℂ} {κ δ : ℝ}
    (hδ : 0 < δ)
    (hmem : ∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ ⊤)
    {t : ℝ} (ht : 0 ≤ t) (hV : v + (t : ℂ) * slantDir κ ∈ VInf ⊤)
    (hX : v + (t : ℂ) * slantDir κ ∉ Pinch) :
    ∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v + (t : ℂ) * slantDir κ ∈ Om σ ⊤ := by
  intro σ hσ hσne
  refine ⟨hV, ?_⟩
  simp only [mem_iUnion, not_exists]
  rintro x hx ⟨s, hs, he⟩
  have hs0 : s ≠ 0 := by
    intro h
    have he' : v + (t : ℂ) * slantDir κ = x := by simpa [h] using he
    exact hX (he'.symm ▸ hx)
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hts : 0 < t + s := by linarith
  let q := (t * κ + s * σ) / (t + s)
  have hq : q ∈ Ioo (κ - δ) (κ + δ) := by
    constructor
    · apply (lt_div_iff₀ hts).mpr
      nlinarith [mul_pos hsp (sub_pos.mpr hσ.1), mul_nonneg ht hδ.le]
    · apply (div_lt_iff₀ hts).mpr
      nlinarith [mul_pos hsp (sub_pos.mpr hσ.2), mul_nonneg ht hδ.le]
  have hqmul : q * (t + s) = t * κ + s * σ := div_mul_cancel₀ _ (ne_of_gt hts)
  have hqne : q ≠ κ := by
    intro heq
    rw [heq] at hqmul
    have hh : s * (σ - κ) = 0 := by nlinarith
    exact hσne (by rcases mul_eq_zero.mp hh with h | h; exact False.elim (hs0 h); linarith)
  apply (hmem q hq hqne).2
  refine mem_iUnion₂.mpr ⟨x, hx, t + s, hts.le, ?_⟩
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp [slantDir] at hr hi
  apply Complex.ext <;> simp [slantDir] <;> nlinarith

/-- The jump for any generic pair in an isolated punctured slope interval. -/
private theorem jump_line_generic (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
     (hK : IsPinchKernel kerG ⊤ G)
    (κ : ℝ) :
    ∀ {v : ℂ}, v ∈ VInf ⊤ → v ∉ Pinch → ∀ {δ : ℝ}, 0 < δ →
      (∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ ⊤) →
      ∀ m ∈ Ioo (κ - δ) κ, ∀ p ∈ Ioo κ (κ + δ),
      IsGenericSlope m → IsGenericSlope p →
      DthMix p =ᶠ[𝓝 v] fun z => DthMix m z + sumMcMix (rayE κ v) z := by
  classical
  have aux : ∀ n : ℕ, ∀ {v : ℂ}, v ∈ VInf ⊤ → v ∉ Pinch →
      (rayE κ v ∩ Xcat).ncard = n → ∀ {δ : ℝ}, 0 < δ →
      (∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ ⊤) →
      ∀ m ∈ Ioo (κ - δ) κ, ∀ p ∈ Ioo κ (κ + δ),
      IsGenericSlope m → IsGenericSlope p →
      DthMix p =ᶠ[𝓝 v] fun z => DthMix m z + sumMcMix (rayE κ v) z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hvX hn δ hδ hmem m hm p hp hmg hpg
      let F := rayE κ v ∩ Xcat
      have hF : F.Finite := rayE_inter_Xcat_finite hZ1 hv κ
      by_cases hne : F.Nonempty
      · obtain ⟨x, hx, hmin⟩ := Set.exists_min_image F Complex.re hF hne
        obtain ⟨s, hs, hxs⟩ := hx.1
        have hxre : x.re = v.re + s := by rw [hxs]; simp [slantDir]
        have hxV : x ∈ Vt ⊤ := by
          refine ⟨by linarith [hv.1.1], ?_⟩
          apply lt_of_lt_of_le _ hK.three_le
          have hh : (x.re : EReal) < ((3 : ℝ) : EReal) :=
            EReal.coe_lt_coe_iff.mpr (by linarith [re_le_two_of_mem_pinch hx.2.1])
          exact hh.trans_eq (by norm_cast)
        obtain ⟨r, hr, hV, hiso, hstep⟩ := local_jump_step hZ1 hZ2 hZ3 hK hm.2 hp.1 hmg hpg hx.2 hxV
        have hwpos : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr (ThmA.slantDir_ne_zero κ)
        let t := min (r / (2 * ‖slantDir κ‖)) (s / 2)
        have ht : 0 < t := lt_min (by positivity) (by positivity)
        have hts : t < s := (min_le_right _ _).trans_lt (half_lt_self hs)
        have htn : ‖(t : ℂ) * slantDir κ‖ < r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
          have htt := min_le_left (r / (2 * ‖slantDir κ‖)) (s / 2)
          change t ≤ r / (2 * ‖slantDir κ‖) at htt
          have := (le_div_iff₀ (by positivity : 0 < 2 * ‖slantDir κ‖)).mp htt
          nlinarith
        let y := x + (t : ℂ) * slantDir κ
        let w := x - (t : ℂ) * slantDir κ
        have hyB : y ∈ ball x r := by simpa [y, mem_ball, dist_eq_norm] using htn
        have hwB : w ∈ ball x r := by simpa [w, mem_ball, dist_eq_norm] using htn
        have hyV : y ∈ VInf ⊤ := hV hyB
        have hwV : w ∈ VInf ⊤ := hV hwB
        have hyrep : y = v + ((s + t : ℝ) : ℂ) * slantDir κ := by
          dsimp [y]; rw [hxs]; push_cast; ring
        have hyX : y ∉ Pinch := by
          intro hyX
          have he := congrArg Complex.re (hiso y hyB hyX)
          dsimp [y] at he
          simp [slantDir] at he
          linarith
        have hymem := east_punctured_mem hδ hmem (by positivity : 0 ≤ s + t)
          (by rw [← hyrep]; exact hyV) (by rw [← hyrep]; exact hyX)
        rw [← hyrep] at hymem
        let F' := rayE κ y ∩ Xcat
        have hF' : F'.Finite := rayE_inter_Xcat_finite hZ1 hyV κ
        have hsub : F' ⊆ F := by
          rintro a ⟨⟨u, hu, he⟩, ha⟩
          refine ⟨⟨s + t + u, by positivity, ?_⟩, ha⟩
          rw [he, hyrep]; push_cast; ring
        have hxn : x ∉ F' := by
          rintro ⟨⟨u, hu, he⟩, -⟩
          have hh := congrArg Complex.re he
          dsimp [y] at hh
          simp [slantDir] at hh
          linarith
        have hlt : F'.ncard < n := by
          rw [← hn]
          exact Set.ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hxn (by rw [he]; exact hx)⟩) hF
        have hi := ih F'.ncard hlt hyV hyX rfl hδ hymem m hm p hp hmg hpg
        have hg : AnalyticOnNhd ℂ (sumMcMix (rayE κ y)) (Vt ⊤) :=
          MSpanK_analyticOn hZ1 hK (sumMc_mem hF')
        have hwest := hstep t ht htn (sumMcMix (rayE κ y)) hg hi
        have hpartition : F = insert x F' := by
          ext a
          constructor
          · intro ha
            by_cases he : a = x
            · exact Or.inl he
            obtain ⟨u, hu, hau⟩ := ha.1
            have hare : a.re = v.re + u := by rw [hau]; simp [slantDir]
            have hsu : s < u := by
              have hl := hmin a ha
              have hne : s ≠ u := by intro heq; apply he; rw [hau, hxs, heq]
              exact lt_of_le_of_ne (by linarith) hne
            have htu : s + t < u := by
              by_contra hno
              have hut : u - s ≤ t := by linarith
              have hax : a - x = ((u - s : ℝ) : ℂ) * slantDir κ := by
                rw [hau, hxs]; push_cast; ring
              have haB : a ∈ ball x r := by
                rw [mem_ball, dist_eq_norm, hax, norm_mul, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hsu)]
                have hh := mul_le_mul_of_nonneg_right hut (norm_nonneg (slantDir κ))
                have htt : t * ‖slantDir κ‖ < r := by simpa [norm_mul, abs_of_pos ht] using htn
                exact hh.trans_lt htt
              exact he (hiso a haB ha.2.1)
            exact Or.inr ⟨⟨u - s - t, by linarith, by rw [hau, hyrep]; push_cast; ring⟩, ha.2⟩
          · rintro (he | ha)
            · exact he ▸ hx
            · exact hsub ha
        have hsum (z : ℂ) : sumMcMix (rayE κ v) z = sumMcMix (rayE κ y) z + McMix x z := by
          change (∑ᶠ a ∈ F, McMix a z) = (∑ᶠ a ∈ F', McMix a z) + McMix x z
          rw [hpartition, finsum_mem_insert _ hxn hF']
          ring
        let U := Om m ⊤ ∩ Om p ⊤
        let q : ℝ → ℂ := fun u => v + (u : ℂ) * slantDir κ
        have hqw : q (s - t) = w := by dsimp [q, w]; rw [hxs]; push_cast; ring
        have hqmem : q '' Icc 0 (s - t) ⊆ U := by
          rintro _ ⟨u, hu, rfl⟩
          have hqV : q u ∈ VInf ⊤ := by
            have hre : (q u).re = v.re + u := by simp [q, slantDir]
            have hwre : w.re = v.re + s - t := by dsimp [w]; rw [hxs]; simp [slantDir]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [hre]; linarith [hv.1.1, hu.1]
            · apply lt_of_le_of_lt _ hwV.1.2
              apply EReal.coe_le_coe_iff.mpr
              rw [hre, hwre]; linarith [hu.2]
            · rw [hre]; linarith [hv.2, hu.1]
          have hqX : q u ∉ Pinch := by
            intro hqX
            by_cases hu0 : u = 0
            · apply hvX; simpa [q, hu0] using hqX
            have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
            have ha : q u ∈ F := ⟨⟨u, hup, rfl⟩, hqX, hqV.2⟩
            have hh := hmin (q u) ha
            simp [q, slantDir, hxre] at hh
            linarith [hu.2]
          have hh := east_punctured_mem hδ hmem hu.1 hqV hqX
          exact ⟨hh m ⟨hm.1, by linarith [hm.2]⟩ (ne_of_lt hm.2),
            hh p ⟨by linarith [hp.1], hp.2⟩ (ne_of_gt hp.1)⟩
        have hG : AnalyticOnNhd ℂ (sumMcMix (rayE κ v)) (Vt ⊤) :=
          MSpanK_analyticOn hZ1 hK (sumMc_mem hF)
        have hew : DthMix p =ᶠ[𝓝 w] fun z => DthMix m z + sumMcMix (rayE κ v) z := by
          filter_upwards [hwest] with z hz
          rw [hsum]
          simpa only [add_assoc] using hz
        apply analytic_germ_transport ((isOpen_Om hZ1 m ⊤).inter (isOpen_Om hZ1 p ⊤))
          (isPreconnected_Icc.image q (by fun_prop)) hqmem
          (show v ∈ q '' Icc 0 (s - t) from ⟨0, ⟨le_rfl, by linarith⟩, by simp [q]⟩)
          (show w ∈ q '' Icc 0 (s - t) from ⟨s - t, ⟨by linarith, le_rfl⟩, hqw⟩)
        · exact (Dth_analyticOn hZ1 hZ2 hZ3 hK p).mono (fun z hz => hz.2)
        · exact ((Dth_analyticOn hZ1 hZ2 hZ3 hK m).mono (fun z hz => hz.1)).add
            (hG.mono (fun z hz => hz.1.1.1))
        · exact hew
      · have hempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hc : v ∈ Om κ ⊤ := (mem_Om_iff_no_ray hv hvX κ).mpr (by
          intro x hx hxr
          have hh : x ∈ F := ⟨hxr, hx⟩
          simpa [hempty] using hh)
        have hall : ∀ σ ∈ Icc m p, v ∈ Om σ ⊤ := by
          intro σ hσ
          by_cases he : σ = κ
          · simpa [he] using hc
          exact hmem σ ⟨by linarith [hm.1, hσ.1], by linarith [hp.2, hσ.2]⟩ he
        have heq := germ_const hZ1 hZ2 hZ3 hK (by linarith [hm.2, hp.1]) hall
        filter_upwards [heq] with z hz
        have hzero : sumMcMix (rayE κ v) z = 0 := by
          change (∑ᶠ a ∈ F, McMix a z) = 0
          simp [hempty]
        simpa [hzero] using hz
  intro v hv hvX δ hδ hmem m hm p hp hmg hpg
  exact aux _ hv hvX rfl hδ hmem m hm p hp hmg hpg

/-- **Jump along one line.** `v₁ ∉ X`; the catalogue points on the open ray in direction `κ` are
finitely many; for slopes close enough on either side, `v₁ ∈ Ω_{κm}, Ω_{κp}` and `D^{κp} - D^{κm} = ∑ M_{x_i}`, as germs. -/
theorem jump_line (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) 
    (hK : IsPinchKernel kerG ⊤ G) {v₁ : ℂ} (hv₁ : v₁ ∈ VInf ⊤) (hv₁X : v₁ ∉ Pinch) (κ : ℝ) :
    (rayE κ v₁ ∩ Xcat).Finite ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ κm ∈ Ioo (κ - δ) κ, ∀ κp ∈ Ioo κ (κ + δ),
      v₁ ∈ Om κm ⊤ ∧ v₁ ∈ Om κp ⊤ ∧
        DthMix κp =ᶠ[𝓝 v₁] fun v => DthMix κm v + sumMcMix (rayE κ v₁) v := by
  obtain ⟨δ, hδ, hmem⟩ := punctured_slopes_mem_Om hZ1 hv₁ hv₁X κ
  obtain ⟨m, hmg, hm⟩ := GoldbachBoundaries.HInf.Fill.generic_cocountable.dense_compl ℝ |>.exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (show κ - δ < κ by linarith))
  obtain ⟨p, hpg, hp⟩ := GoldbachBoundaries.HInf.Fill.generic_cocountable.dense_compl ℝ |>.exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (show κ < κ + δ by linarith))
  have hmg' : IsGenericSlope m := by simpa using hmg
  have hpg' : IsGenericSlope p := by simpa using hpg
  have heq := jump_line_generic hZ1 hZ2 hZ3 hK κ hv₁ hv₁X hδ hmem m hm p hp hmg' hpg'
  have hsame {a b : ℝ} (ha : a ∈ Ioo (κ - δ) κ) (hb : b ∈ Ioo (κ - δ) κ) :
      DthMix a =ᶠ[𝓝 v₁] DthMix b := by
    rcases le_total a b with hab | hba
    · exact (germ_const hZ1 hZ2 hZ3 hK hab (fun σ hσ => hmem σ
        ⟨by linarith [ha.1, hσ.1], by linarith [hb.2, hσ.2]⟩ (by linarith [hb.2, hσ.2]))).symm
    · exact germ_const hZ1 hZ2 hZ3 hK hba (fun σ hσ => hmem σ
        ⟨by linarith [hb.1, hσ.1], by linarith [ha.2, hσ.2]⟩ (by linarith [ha.2, hσ.2]))
  have hsame' {a b : ℝ} (ha : a ∈ Ioo κ (κ + δ)) (hb : b ∈ Ioo κ (κ + δ)) :
      DthMix a =ᶠ[𝓝 v₁] DthMix b := by
    rcases le_total a b with hab | hba
    · exact (germ_const hZ1 hZ2 hZ3 hK hab (fun σ hσ => hmem σ
        ⟨by linarith [ha.1, hσ.1], by linarith [hb.2, hσ.2]⟩ (by linarith [ha.1, hσ.1]))).symm
    · exact germ_const hZ1 hZ2 hZ3 hK hba (fun σ hσ => hmem σ
        ⟨by linarith [hb.1, hσ.1], by linarith [ha.2, hσ.2]⟩ (by linarith [hb.1, hσ.1]))
  refine ⟨rayE_inter_Xcat_finite hZ1 hv₁ κ, δ, hδ, ?_⟩
  intro κm hκm κp hκp
  refine ⟨hmem κm ⟨hκm.1, by linarith [hκm.2]⟩ (ne_of_lt hκm.2),
    hmem κp ⟨by linarith [hκp.1], hκp.2⟩ (ne_of_gt hκp.1), ?_⟩
  filter_upwards [heq, hsame hκm hm, hsame' hκp hp] with v hv hvm hvp
  rw [hvp, hv, ← hvm]

end GoldbachBoundaries.HInf.MixProof
