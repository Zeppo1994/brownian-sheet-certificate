import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
namespace BrownianSharp.AlignmentPaperCompactTubes

def closedTube {X : Type*} [MetricSpace X] (K : Set X) (ε : ℝ) : Set X :=
  {x | ∃ y ∈ K, dist x y≤ε}

/-- A closed-radius tube around a nonempty compact set is closed. Its
measurability is inherited from Mathlib's continuous distance-to-set map. -/
theorem closedTube_isClosed {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) (ε : ℝ) :
    IsClosed (closedTube K ε) := by
  have heq : closedTube K ε={x | Metric.infDist x K≤ε} := by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact (Metric.infDist_le_dist_of_mem hy).trans hxy
    · intro hx
      obtain ⟨y,hy,he⟩ := hK.exists_infDist_eq_dist hne x
      exact ⟨y,hy,by rw [←he]; exact hx⟩
  rw [heq]
  exact isClosed_le (Metric.continuous_infDist_pt K) continuous_const

end BrownianSharp.AlignmentPaperCompactTubes
