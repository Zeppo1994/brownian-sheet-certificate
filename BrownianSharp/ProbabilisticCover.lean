import BrownianSharp.TheoremDEntropyPacking
import Mathlib.MeasureTheory.Measure.Basic

/-!
The manuscript's Gaussian-cover argument as a general measure-theoretic
lemma. Centered small-ball estimates and admissible-class mass enter exactly
where stated; no Gaussian inequality or atomic synthesis is assumed here.
-/
open MeasureTheory
open scoped NNReal ENNReal

namespace BrownianSharp

/-- A finite ambient-center cover of the class covers the admissible event.
A uniform translated-ball probability bound controls its mass. -/
theorem admissible_mass_le_finite_cover
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace X]
    (P : Measure Ω) (F : Ω → X) (E : Set Ω) (K : Set X)
    (ρ : NNReal) (s : Finset X)
    (hcover : Metric.IsCover ρ K (s : Set X))
    (hclass : ∀ ω ∈ E, F ω ∈ K) (q : ENNReal)
    (hball : ∀ x : X, P {ω | edist (F ω) x ≤ ρ} ≤ q) :
    P E ≤ (s.card : ENNReal) * q := by
  have hsub : E ⊆ ⋃ x ∈ s, {ω | edist (F ω) x ≤ ρ} := by
    intro ω hω
    obtain ⟨x, hx, hdist⟩ := hcover (hclass ω hω)
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hdist⟩⟩
  calc
    P E ≤ P (⋃ x ∈ s, {ω | edist (F ω) x ≤ ρ}) := measure_mono hsub
    _ ≤ ∑ x ∈ s, P {ω | edist (F ω) x ≤ ρ} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ s, q := Finset.sum_le_sum fun x _ => hball x
    _ = (s.card : ENNReal) * q := by simp

/-- If m balls cannot carry the admissible mass, the actual external
covering number exceeds m, including the possibility of an infinite cover. -/
theorem externalCoveringNumber_gt_of_admissible_mass
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace X]
    (P : Measure Ω) (F : Ω → X) (E : Set Ω) (K : Set X)
    (ρ : NNReal) (q : ENNReal) (m : ℕ)
    (hclass : ∀ ω ∈ E, F ω ∈ K)
    (hball : ∀ x : X, P {ω | edist (F ω) x ≤ ρ} ≤ q)
    (hmass : (m : ENNReal) * q < P E) :
    (m : ENat) < Metric.externalCoveringNumber ρ K := by
  classical
  apply ENat.natCast_add_one_le_iff.mp
  unfold Metric.externalCoveringNumber
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  by_cases hfinite : C.Finite
  · have hbound := admissible_mass_le_finite_cover P F E K ρ hfinite.toFinset
      (by simpa using hC) hclass q hball
    have hcard : m < hfinite.toFinset.card := by
      by_contra hnot
      have hle : hfinite.toFinset.card ≤ m := Nat.le_of_not_gt hnot
      have hcast : (hfinite.toFinset.card : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast hle
      exact (not_le_of_gt hmass) (hbound.trans (mul_le_mul_of_nonneg_right hcast (show 0 ≤ q from bot_le)))
    have hcast : ((m + 1 : ℕ) : ENat) ≤ (hfinite.toFinset.card : ENat) := by
      exact_mod_cast Nat.succ_le_of_lt hcard
    rw [hfinite.encard_eq_coe_toFinset_card]
    exact hcast
  · simp [Set.Infinite.encard_eq hfinite]

end BrownianSharp
