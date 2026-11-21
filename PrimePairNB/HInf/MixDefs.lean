import PrimePairNB.HInf.Defs

/-! The mixed series, sheet, and varying coefficient. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

def Wlogq (s : ℂ) (p q : ℕ) : ℂ := (Real.log q : ℂ) * WG s p q
abbrev MixSer : ℂ → ℂ := Dser Wlogq

def AdmMix (g : ℂ → ℂ) (s₁ : ℂ) : Prop :=
  IsAdmissibleGermOn MixSer
    (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁

def betaMix (u : ℂ) : ℂ := kerG 1 (1 + u) + kerG u (1 + u)

def XcMix (x s : ℂ) : ℂ :=
  -∑' p : pinchPairs x, cP p.1.1 * cP p.1.2 * kerG (s - p.1.2) s

def pairIntegrandMix (κ : ℝ) (s z : ℂ) : ℂ :=
  kerG z s * Pth κ z * Qcont (s - z)

def DthMix (κ : ℝ) (s : ℂ) : ℂ := by
  classical
  exact if h : ∃ Γ : SlantGraph κ, IsSeparating s Γ then
    graphInt h.choose (pairIntegrandMix κ s) else 0

def McMix (x : ℂ) (s : ℂ) : ℂ := 2 * (Real.pi : ℂ) * I * XcMix x s

def MSpanMix : AddSubgroup (ℂ → ℂ) := AddSubgroup.closure (McMix '' Xcat)

def GermFamMix (C q : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ κ : ℝ, q ∈ Om κ ⊤ ∧ ∃ m ∈ MSpanMix,
    f =ᶠ[𝓝 q] fun s => DthMix κ s + m s + C

end GoldbachBoundaries.HInf
