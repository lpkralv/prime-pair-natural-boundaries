import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.germ_const
import PrimePairNB.HInf.Fill.jump_line_transport
import PrimePairNB.HInf.Fill.sumMc_mem
import PrimePairNB.HInf.Fill.pinch_countable
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-! The one-line jump, transported east to west through its finite catalogue.
All analytic and geometric inputs are imported from the lemmas proved in this folder. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

def lineSlope (v x : ℂ) : ℝ := (x - v).im / (x - v).re

theorem lineSlope_repr {v x : ℂ} (h : 0 < (x - v).re) :
    x = v + (((x - v).re : ℝ) : ℂ) * slantDir (lineSlope v x) := by
  apply Complex.ext
  · simp [slantDir]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    have him : (slantDir (lineSlope v x)).im = lineSlope v x := by simp [slantDir]
    rw [him]
    dsimp [lineSlope]
    change 0 < x.re - v.re at h
    rw [mul_div_cancel₀ _ (ne_of_gt h)]
    simp

theorem lineSlope_add (v : ℂ) {t : ℝ} (ht : t ≠ 0) (κ : ℝ) :
    lineSlope v (v + (t : ℂ) * slantDir κ) = κ := by
  simp [lineSlope, slantDir, ht]

theorem mem_rayE_iff_lineSlope {v x : ℂ} {κ : ℝ} :
    x ∈ rayE κ v ↔ 0 < (x - v).re ∧ lineSlope v x = κ := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa [slantDir] using ht, lineSlope_add v (ne_of_gt ht) κ⟩
  · rintro ⟨ht, he⟩
    exact ⟨(x - v).re, ht, he ▸ lineSlope_repr ht⟩

theorem mem_sector_iff_lineSlope {v x : ℂ} {a b : ℝ} :
    x ∈ sector v a b ↔ 0 < (x - v).re ∧ lineSlope v x ∈ Ioo a b := by
  constructor
  · rintro ⟨t, ht, σ, hσ, rfl⟩
    exact ⟨by simpa [slantDir] using ht, by simpa [lineSlope_add v (ne_of_gt ht)] using hσ⟩
  · rintro ⟨ht, hσ⟩
    exact ⟨(x - v).re, ht, lineSlope v x, hσ, lineSlope_repr ht⟩

theorem not_mem_Pinch_of_mem_Om {top : EReal} {v : ℂ} {κ : ℝ}
    (hv : v ∈ Om κ top) : v ∉ Pinch := by
  intro h
  exact hv.2 (mem_iUnion₂.mpr ⟨v, h, 0, le_rfl, by simp⟩)

theorem mem_Om_iff_no_ray {top : EReal} {v : ℂ} (hv : v ∈ VInf top)
    (hvX : v ∉ Pinch) (κ : ℝ) :
    v ∈ Om κ top ↔ ∀ x ∈ Xcat, x ∉ rayE κ v := by
  constructor
  · intro hm x hx hxray
    obtain ⟨t, ht, he⟩ := hxray
    apply hm.2
    refine mem_iUnion₂.mpr ⟨x, hx.1, t, ht.le, ?_⟩
    linear_combination -he
  · intro hm
    refine ⟨hv, ?_⟩
    simp only [mem_iUnion, not_exists]
    rintro x hx ⟨t, ht, he⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      have hvx : v = x := by simpa [ht0] using he
      exact hvX (hvx ▸ hx)
    have hxrep : x = v + (t : ℂ) * slantDir κ := by linear_combination -he
    have hxcat : x ∈ Xcat := by
      refine ⟨hx, ?_⟩
      rw [hxrep]
      simp [slantDir]
      linarith [hv.2]
    exact hm x hxcat ⟨t, lt_of_le_of_ne ht (Ne.symm ht0), hxrep⟩

/-- A bounded closed sector of candidate pinches is compact and remains to the
right of the abscissa of its vertex. -/
theorem finite_candidate_pinches (hZ1 : Z1) {v : ℂ} (hv : 2 * Binf < v.re)
    (a b : ℝ) :
    (((fun p : ℝ × ℝ => v + (p.1 : ℂ) * slantDir p.2) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc a b)) ∩ Pinch).Finite := by
  apply finite_inter_pinch hZ1
    ((isCompact_Icc.prod isCompact_Icc).image (by unfold slantDir; fun_prop))
  rintro _ ⟨⟨t, σ⟩, ⟨ht, hσ⟩, rfl⟩
  show 2 * Binf < (v + (t : ℂ) * slantDir σ).re
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have : (slantDir σ).re = 1 := by simp [slantDir]
  rw [this, mul_one]
  linarith [ht.1]

/-- The finite-set assertion in `jump_line`. -/
theorem rayE_inter_Xcat_finite (hZ1 : Z1) {top : EReal} {v₁ : ℂ}
    (hv₁ : v₁ ∈ VInf top) (κ : ℝ) : (rayE κ v₁ ∩ Xcat).Finite := by
  apply (finite_candidate_pinches hZ1 hv₁.2 κ κ).subset
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  refine ⟨⟨(t, κ), ⟨⟨ht.le, ?_⟩, le_rfl, le_rfl⟩, rfl⟩, hx.1⟩
  have hre := re_le_two_of_mem_pinch hx.1
  have hv := hv₁.1.1
  simp [slantDir] at hre
  linarith

/-- The finite-set assertion in `rotation`. -/
theorem sector_inter_Xcat_finite (hZ1 : Z1) {top : EReal} {v₁ : ℂ}
    (hv₁ : v₁ ∈ VInf top) (κ κ' : ℝ) : (sector v₁ κ κ' ∩ Xcat).Finite := by
  apply (finite_candidate_pinches hZ1 hv₁.2 κ κ').subset
  rintro x ⟨⟨t, ht, σ, hσ, rfl⟩, hx⟩
  refine ⟨⟨(t, σ), ⟨⟨ht.le, ?_⟩, hσ.1.le, hσ.2.le⟩, rfl⟩, hx.1⟩
  have hre := re_le_two_of_mem_pinch hx.1
  have hv := hv₁.1.1
  simp [slantDir] at hre
  linarith

/-- A point off the pinch set belongs to every nearby sheet except possibly
the sheet at the central slope. This includes nongeneric slopes. -/
theorem punctured_slopes_mem_Om (hZ1 : Z1) {top : EReal} {v₁ : ℂ}
    (hv₁ : v₁ ∈ VInf top) (hv₁X : v₁ ∉ Pinch) (κ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v₁ ∈ Om σ top := by
  classical
  let K : Set ℂ := (fun p : ℝ × ℝ => v₁ + (p.1 : ℂ) * slantDir p.2) ''
    (Icc (0 : ℝ) 1 ×ˢ Icc (κ - 1) (κ + 1))
  let slope : ℂ → ℝ := fun x => (x - v₁).im / (x - v₁).re
  have hF : (K ∩ Pinch).Finite := finite_candidate_pinches hZ1 hv₁.2 (κ - 1) (κ + 1)
  have hclosed : IsClosed ((slope '' (K ∩ Pinch)) \ {κ}) :=
    (hF.image slope).sdiff.isClosed
  have hκ : κ ∈ ((slope '' (K ∩ Pinch)) \ {κ})ᶜ := by simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl κ hκ
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro σ hσ hσne
  have hσr : σ ∈ ball κ r := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hσ.1, hσ.2, min_le_left r 1]
  have hσ1 : σ ∈ Icc (κ - 1) (κ + 1) := by
    constructor <;> linarith [hσ.1, hσ.2, min_le_right r 1]
  refine ⟨hv₁, ?_⟩
  simp only [mem_iUnion, not_exists]
  rintro x hx ⟨t, ht, heq⟩
  have ht0 : t ≠ 0 := by
    intro he
    apply hv₁X
    have hvx : v₁ = x := by simpa [he] using heq
    exact hvx ▸ hx
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hxrep : x = v₁ + (t : ℂ) * slantDir σ := by
    linear_combination -heq
  have ht1 : t ≤ 1 := by
    have hre := re_le_two_of_mem_pinch hx
    rw [hxrep] at hre
    simp [slantDir] at hre
    linarith [hv₁.1.1]
  have hxK : x ∈ K := ⟨(t, σ), ⟨⟨ht, ht1⟩, hσ1⟩, hxrep.symm⟩
  have hslope : slope x = σ := by
    rw [hxrep]
    simp [slope, slantDir, ht0]
  apply hball hσr
  exact ⟨⟨x, ⟨hxK, hx⟩, hslope⟩, by simpa using hσne⟩

/-- Every nearby noncentral slope remains clear along the original east ray,
until a catalogue point itself is reached. -/
private lemma east_punctured_mem {top : EReal} {v : ℂ} {κ δ : ℝ}
    (hδ : 0 < δ)
    (hmem : ∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ top)
    {t : ℝ} (ht : 0 ≤ t) (hV : v + (t : ℂ) * slantDir κ ∈ VInf top)
    (hX : v + (t : ℂ) * slantDir κ ∉ Pinch) :
    ∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v + (t : ℂ) * slantDir κ ∈ Om σ top := by
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
    {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D)
    (κ : ℝ) :
    ∀ {v : ℂ}, v ∈ VInf top → v ∉ Pinch → ∀ {δ : ℝ}, 0 < δ →
      (∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ top) →
      ∀ m ∈ Ioo (κ - δ) κ, ∀ p ∈ Ioo κ (κ + δ),
      IsGenericSlope m → IsGenericSlope p →
      Dth k p =ᶠ[𝓝 v] fun z => Dth k m z + sumMc k (rayE κ v) z := by
  classical
  have aux : ∀ n : ℕ, ∀ {v : ℂ}, v ∈ VInf top → v ∉ Pinch →
      (rayE κ v ∩ Xcat).ncard = n → ∀ {δ : ℝ}, 0 < δ →
      (∀ σ ∈ Ioo (κ - δ) (κ + δ), σ ≠ κ → v ∈ Om σ top) →
      ∀ m ∈ Ioo (κ - δ) κ, ∀ p ∈ Ioo κ (κ + δ),
      IsGenericSlope m → IsGenericSlope p →
      Dth k p =ᶠ[𝓝 v] fun z => Dth k m z + sumMc k (rayE κ v) z := by
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
        have hxV : x ∈ Vt top := by
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
        have hyV : y ∈ VInf top := hV hyB
        have hwV : w ∈ VInf top := hV hwB
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
        have hg : AnalyticOnNhd ℂ (sumMc k (rayE κ y)) (Vt top) :=
          MSpanK_analyticOn hZ1 hK (sumMc_mem k hF')
        have hwest := hstep t ht htn (sumMc k (rayE κ y)) hg hi
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
        have hsum (z : ℂ) : sumMc k (rayE κ v) z = sumMc k (rayE κ y) z + Mc k x z := by
          change (∑ᶠ a ∈ F, Mc k a z) = (∑ᶠ a ∈ F', Mc k a z) + Mc k x z
          rw [hpartition, finsum_mem_insert _ hxn hF']
          ring
        let U := Om m top ∩ Om p top
        let q : ℝ → ℂ := fun u => v + (u : ℂ) * slantDir κ
        have hqw : q (s - t) = w := by dsimp [q, w]; rw [hxs]; push_cast; ring
        have hqmem : q '' Icc 0 (s - t) ⊆ U := by
          rintro _ ⟨u, hu, rfl⟩
          have hqV : q u ∈ VInf top := by
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
        have hG : AnalyticOnNhd ℂ (sumMc k (rayE κ v)) (Vt top) :=
          MSpanK_analyticOn hZ1 hK (sumMc_mem k hF)
        have hew : Dth k p =ᶠ[𝓝 w] fun z => Dth k m z + sumMc k (rayE κ v) z := by
          filter_upwards [hwest] with z hz
          rw [hsum]
          simpa only [add_assoc] using hz
        apply analytic_germ_transport ((isOpen_Om hZ1 m top).inter (isOpen_Om hZ1 p top))
          (isPreconnected_Icc.image q (by fun_prop)) hqmem
          (show v ∈ q '' Icc 0 (s - t) from ⟨0, ⟨le_rfl, by linarith⟩, by simp [q]⟩)
          (show w ∈ q '' Icc 0 (s - t) from ⟨s - t, ⟨by linarith, le_rfl⟩, hqw⟩)
        · exact (RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK p).mono (fun z hz => hz.2)
        · exact ((RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK m).mono (fun z hz => hz.1)).add
            (hG.mono (fun z hz => hz.1.1.1))
        · exact hew
      · have hempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hc : v ∈ Om κ top := (mem_Om_iff_no_ray hv hvX κ).mpr (by
          intro x hx hxr
          have hh : x ∈ F := ⟨hxr, hx⟩
          simpa [hempty] using hh)
        have hall : ∀ σ ∈ Icc m p, v ∈ Om σ top := by
          intro σ hσ
          by_cases he : σ = κ
          · simpa [he] using hc
          exact hmem σ ⟨by linarith [hm.1, hσ.1], by linarith [hp.2, hσ.2]⟩ he
        have heq := germ_const hZ1 hZ2 hZ3 hK (by linarith [hm.2, hp.1]) hall
        filter_upwards [heq] with z hz
        have hzero : sumMc k (rayE κ v) z = 0 := by
          change (∑ᶠ a ∈ F, Mc k a z) = 0
          simp [hempty]
        simpa [hzero] using hz
  intro v hv hvX δ hδ hmem m hm p hp hmg hpg
  exact aux _ hv hvX rfl hδ hmem m hm p hp hmg hpg

/-- **Jump along one line.** `v₁ ∉ X`; the catalogue points on the open ray in direction `κ` are
finitely many; for slopes close enough on either side, `v₁ ∈ Ω_{κm}, Ω_{κp}` and `D^{κp} - D^{κm} = ∑ M_{x_i}`, as germs. -/
theorem jump_line (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {v₁ : ℂ} (hv₁ : v₁ ∈ VInf top) (hv₁X : v₁ ∉ Pinch) (κ : ℝ) :
    (rayE κ v₁ ∩ Xcat).Finite ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ κm ∈ Ioo (κ - δ) κ, ∀ κp ∈ Ioo κ (κ + δ),
      v₁ ∈ Om κm top ∧ v₁ ∈ Om κp top ∧
        Dth k κp =ᶠ[𝓝 v₁] fun v => Dth k κm v + sumMc k (rayE κ v₁) v := by
  obtain ⟨δ, hδ, hmem⟩ := punctured_slopes_mem_Om hZ1 hv₁ hv₁X κ
  obtain ⟨m, hmg, hm⟩ := GoldbachBoundaries.HInf.Fill.generic_cocountable.dense_compl ℝ |>.exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (show κ - δ < κ by linarith))
  obtain ⟨p, hpg, hp⟩ := GoldbachBoundaries.HInf.Fill.generic_cocountable.dense_compl ℝ |>.exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (show κ < κ + δ by linarith))
  have hmg' : IsGenericSlope m := by simpa using hmg
  have hpg' : IsGenericSlope p := by simpa using hpg
  have heq := jump_line_generic hZ1 hZ2 hZ3 hK κ hv₁ hv₁X hδ hmem m hm p hp hmg' hpg'
  have hsame {a b : ℝ} (ha : a ∈ Ioo (κ - δ) κ) (hb : b ∈ Ioo (κ - δ) κ) :
      Dth k a =ᶠ[𝓝 v₁] Dth k b := by
    rcases le_total a b with hab | hba
    · exact (germ_const hZ1 hZ2 hZ3 hK hab (fun σ hσ => hmem σ
        ⟨by linarith [ha.1, hσ.1], by linarith [hb.2, hσ.2]⟩ (by linarith [hb.2, hσ.2]))).symm
    · exact germ_const hZ1 hZ2 hZ3 hK hba (fun σ hσ => hmem σ
        ⟨by linarith [hb.1, hσ.1], by linarith [ha.2, hσ.2]⟩ (by linarith [ha.2, hσ.2]))
  have hsame' {a b : ℝ} (ha : a ∈ Ioo κ (κ + δ)) (hb : b ∈ Ioo κ (κ + δ)) :
      Dth k a =ᶠ[𝓝 v₁] Dth k b := by
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

end GoldbachBoundaries.HInf.Fill

