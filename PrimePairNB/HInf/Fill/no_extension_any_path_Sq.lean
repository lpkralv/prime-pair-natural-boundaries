import PrimePairNB.HInf.MixFollowCommon
import PrimePairNB.HInf.SqFollowTransport

noncomputable section

open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- A terminal prime-square germ cannot extend meromorphically across `Re s = 1/2`,
including when the path ends at a catalogue point. -/
theorem no_extension_any_path_Sq (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm SqSer γ g)
    (y r : ℝ) (hr : 0 < r) (h1 : γ 1 ∈ ball ((1/2 : ℂ) + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g (γ 1) (ball ((1/2 : ℂ) + (y : ℂ) * I) r) := by
  let δ : C(unitInterval, ℂ) := ⟨fun t => 2 * γ t, by fun_prop⟩
  have hδ0 : 2 < (δ 0).re := by change 2 < (2 * γ 0).re; simp; linarith
  let c : ℂ := 1 + ((2 * y : ℝ) : ℂ) * I
  have hc : c / 2 = (1/2 : ℂ) + (y : ℂ) * I := by
    dsimp [c]
    push_cast
    ring
  have hball (v : ℂ) : v ∈ ball c (2 * r) ↔ v / 2 ∈ ball (c / 2) r := by
    rw [mem_ball, mem_ball, dist_sq_half]
    constructor <;> intro h <;> linarith
  have hδ1 : δ 1 ∈ ball c (2 * r) :=
    (hball (δ 1)).mpr (by simpa only [δ, ContinuousMap.coe_mk, SqFollow.half_double, hc] using h1)
  rintro ⟨-, M, hMm, hMg⟩
  obtain ⟨M', hM'm, hM'g, -⟩ := ThmA.exists_meromorphic_update hMm hMg
  refine Follow.no_extension_any_path (F := DSq) (γ := δ) hH hZ1 (fun _ hs => DSq_analyticAt hs)
    (fun _ _ had => boundary_SqV hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 had)
    hδ0 (SqFollow.terminal_double hg) (2 * y) (2 * r) (by linarith) hδ1
    ⟨hδ1, fun v => M' (v / 2), fun v hv => ?_, ?_⟩
  · have hv' := (hball v).mp hv
    rw [hc] at hv'
    exact (hM'm (v / 2) hv').comp_analyticAt (g := fun v : ℂ => v / 2) (by fun_prop)
  · exact (eventuallyEq_comp_sq_half hM'g).filter_mono nhdsWithin_le_nhds

end GoldbachBoundaries.HInf.Fill
