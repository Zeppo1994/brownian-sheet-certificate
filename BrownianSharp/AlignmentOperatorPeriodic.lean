import BrownianSharp.AlignmentLatestNikolskyWidths
import BrownianSharp.AlignmentLatestPeriodicEntropy
import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentOperatorWidthIndexShift

/-! Periodic clauses for the revised manuscript's L-infinity entropy and
strict-dimension operator widths. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentOperatorPeriodic

open BrownianSharp.Latest
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentLatestPeriodicEntropy
open BrownianSharp.AlignmentLatestNikolskyWidths
open BrownianSharp.AlignmentLatestPeriodicWidths
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open HaarQuarter.TheoremD.Width

private theorem operator_width_rate_of_legacy
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a)
    (hlegacy : Latest.twoSidedWidthRate K r a) :
    AlignmentOperatorStatements.twoSidedWidthRate K r a := by
  obtain ⟨c,C,hc,hC,k₀,hk₀,hwidth⟩ := hlegacy
  let k₁ := max (k₀+1) 3
  have hk₁ : 3 ≤ k₁ := by dsimp [k₁]; omega
  have hk₀' : k₀+1 ≤ k₁ := by dsimp [k₁]; exact le_max_left _ _
  obtain ⟨c',C',hc',hC',hshift⟩ :=
    twoSided_width_index_shift K r a hr ha c C hc hC k₁ hk₁ (by
      intro k hk
      have hkm : k₀ ≤ k-1 := by omega
      exact hwidth (k-1) hkm)
  refine ⟨c',C',hc',hC',k₁,by omega,?_⟩
  intro k hk
  have hkpos : 1 ≤ k := by omega
  have hEq := operatorKolmogorovNumber_eq_width_pred K hkpos
  simpa only [hEq] using hshift k hk

/-- Theorem 4.1 entropy lower bounds in the actual periodic `L∞` ambient
space. The factor two is the ambient-center covering transfer. -/
theorem periodic_mixed_entropy_certified :
    AlignmentOperatorStatements.PeriodicMixedEntropyStatement := by
  intro d hd p hp r hpr θ hθ
  obtain ⟨c,hc,k₀,hk₀,hlegacy⟩ :=
    (latest_periodicMixedEntropy_certified d hd p hp r hpr θ hθ)
  refine ⟨c/2,by positivity,k₀,hk₀,?_⟩
  intro k hk
  obtain ⟨hs,hb,hn⟩ := hlegacy k hk
  have hBes := periodic_entropy_lower_to_LInfinity
    ({f : RealPeriodic d | BesovUnitBall p r θ f}) k
    (c*logarithmicIndexRate r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) k) hb
  have hNik := periodic_entropy_lower_to_LInfinity
    ({f : RealPeriodic d | NikolskyUnitBall p r f}) k
    (c*logarithmicIndexRate r ((r+1/2)*(d-1:ℕ)+1/2) k) hn
  refine ⟨?_, ?_, ?_⟩
  · intro hpTop
    have hSob := periodic_entropy_lower_to_LInfinity
      ({f : RealPeriodic d | SobolevUnitBall p.toReal r f}) k
      (c*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k) (hs hpTop)
    convert hSob using 1 <;> congr 1 <;> ring
  · convert hBes using 1 <;> congr 1 <;> ring
  · convert hNik using 1 <;> congr 1 <;> ring

/-- The periodic two-sided width clause for strict operator dimensions. -/
theorem periodic_width_certified :
    AlignmentOperatorStatements.PeriodicWidthStatement := by
  intro d hd p hp r hr
  have hrpos : 0 < r := by linarith
  have hsob : p ≠ ⊤ →
      AlignmentOperatorStatements.twoSidedWidthRate
        (Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall p.toReal r f})
        r (r*(d-1:ℕ)+1/2) := by
    intro hptop
    have hlegacy := latest_periodic_sobolev_width (d:=d) hd p hp r hr hptop
    apply operator_width_rate_of_legacy _ _ _ hrpos (by positivity) hlegacy
  have hniklegacy := periodic_nikolsky_twoSided_width (d:=d) hd p hp r hr
  have hnik := operator_width_rate_of_legacy _ _ _ hrpos (by positivity) hniklegacy
  exact ⟨hsob,hnik⟩

end BrownianSharp.AlignmentOperatorPeriodic
