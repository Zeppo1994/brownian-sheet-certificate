import BrownianSharp.TheoremDEntropyPacking
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Tactic

/-! Compactness from the actual entropy-number definition. This lets the
proved periodic entropy estimates discharge compactness needed for uniform
smoothing, without postulating a compact image. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperEntropyCompactness

variable {X : Type*} [MetricSpace X]

theorem totallyBounded_of_entropy_vanishes (K : Set X)
    (hvanish : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ,
      HaarQuarter.TheoremD.entropyNumber k K < (ε : ℝ≥0∞)) :
    TotallyBounded K := by
  apply Metric.totallyBounded_iff.2
  intro ε hε
  let εN : ℝ≥0 := ⟨ε,hε.le⟩
  obtain ⟨k,hk⟩ := hvanish εN hε
  unfold HaarQuarter.TheoremD.entropyNumber at hk
  obtain ⟨r,hr,hsmall⟩ := (sInf_lt_iff).mp hk
  obtain ⟨ρ,rfl,hcover⟩ := hr
  have hρ : (ρ:ℝ) < ε := by exact_mod_cast hsmall
  have hfinite : Metric.externalCoveringNumber ρ K < ⊤ :=
    hcover.trans_lt (ENat.natCast_lt_top _)
  simp only [Metric.externalCoveringNumber, iInf_lt_top, Set.encard_lt_top_iff] at hfinite
  obtain ⟨C,hC,hCfinite⟩ := hfinite
  refine ⟨C,hCfinite,?_⟩
  intro x hx
  obtain ⟨c,hc,hxc⟩ := hC hx
  apply Set.mem_iUnion.2
  refine ⟨c,Set.mem_iUnion.2 ⟨hc,?_⟩⟩
  apply Metric.mem_ball.2
  have hd : dist x c ≤ (ρ:ℝ) := by
    change edist x c ≤ (ρ:ℝ≥0∞) at hxc
    apply (ENNReal.ofReal_le_ofReal_iff ρ.coe_nonneg).mp
    simpa only [← edist_dist, ENNReal.ofReal_coe_nnreal] using hxc
  exact hd.trans_lt hρ

end BrownianSharp.AlignmentPaperEntropyCompactness
