import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement
import Mathlib.SetTheory.Cardinal.NatCard
import BrownianSharp.CameronMartin
import BrownianSharp.EntropyCoverInversion
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open scoped ENNReal NNReal
open HaarQuarter

namespace BrownianSharp.AlignmentAuditLifting

variable {K : Type*} [MetricSpace K]
variable {n : ℕ}

/-- A finite pointwise maximum, with zero included as the empty-family value. -/
def finiteMax (l : List (Fin n)) (g : Fin n → K → ℝ) : K → ℝ :=
  l.foldr (fun i acc x => max (g i x) (acc x)) 0

lemma finiteMax_lipschitz (l : List (Fin n)) (g : Fin n → K → ℝ)
    (hg : ∀ i ∈ l, LipschitzWith 1 (g i)) :
    LipschitzWith 1 (finiteMax l g) := by
  induction l with
  | nil =>
      change LipschitzWith 1 (fun _ : K => (0 : ℝ))
      exact LipschitzWith.of_le_add (fun _ _ => by simp)
  | cons i l ih =>
    have hi : LipschitzWith 1 (g i) := hg i (by simp)
    have htail : LipschitzWith 1 (fun x : K => finiteMax l g x) := by
      apply ih
      intro j hj
      exact hg j (by simp [hj])
    simpa [finiteMax] using hi.max htail

lemma bump_lipschitz (δ : ℝ) (c : K) :
    LipschitzWith 1 (fun x : K => max (δ - dist x c) 0) := by
  have hraw : LipschitzWith 1 (fun x : K => δ - dist x c) := by
    refine LipschitzWith.of_le_add fun x y => ?_
    have hxy : dist y c ≤ dist x c + dist x y := by
      calc
        dist y c ≤ dist y x + dist x c := dist_triangle y x c
        _ = dist x c + dist x y := by rw [dist_comm y x, add_comm]
    linarith
  exact hraw.max_const 0

/-- The finite bump superposition associated to a binary labeling of finitely
many centers. -/
def bitBump (δ : ℝ) (centers : Fin n → K) (bits : Fin n → Bool) : K → ℝ :=
  finiteMax (List.finRange n) (fun i x =>
    if bits i then max (δ - dist x (centers i)) 0 else 0)

lemma bitBump_lipschitz (δ : ℝ) (centers : Fin n → K) (bits : Fin n → Bool) :
    LipschitzWith 1 (bitBump δ centers bits) := by
  apply finiteMax_lipschitz
  intro i hi
  by_cases hb : bits i
  · simpa [bitBump, hb] using bump_lipschitz δ (centers i)
  · simpa [bitBump, hb] using
      (LipschitzWith.of_le_add (fun _ _ => by simp) : LipschitzWith 1 (fun _ : K => (0 : ℝ)))

/-- The bump superposition viewed as a bounded continuous function on a
compact metric space. -/
noncomputable def bitBumpBCF [CompactSpace K] (δ : ℝ) (centers : Fin n → K)
    (bits : Fin n → Bool) : BoundedContinuousFunction K ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨bitBump δ centers bits, (bitBump_lipschitz δ centers bits).continuous⟩

@[simp] lemma bitBumpBCF_apply [CompactSpace K] (δ : ℝ) (centers : Fin n → K)
    (bits : Fin n → Bool) (x : K) : bitBumpBCF δ centers bits x = bitBump δ centers bits x := rfl

/-- A strict external-covering lower bound forces a finite separated packing
of every smaller prescribed cardinality. This is the internal/external
covering-number comparison followed by the packing supremum definition. -/
theorem exists_finite_packing_of_externalCoveringNumber_gt
    {X : Type*} [PseudoEMetricSpace X] (K : Set X) (δ : ℝ≥0) (M : ℕ)
    (hcover : (M : ℕ∞) < Metric.externalCoveringNumber δ K) :
    ∃ S : Finset X, (↑S : Set X) ⊆ K ∧
      Metric.IsSeparated (δ : ℝ≥0∞) (↑S : Set X) ∧ M < S.card := by
  have hpack : (M : ℕ∞) < Metric.packingNumber δ K :=
    lt_of_lt_of_le hcover
      ((Metric.externalCoveringNumber_le_coveringNumber δ K).trans
        (Metric.coveringNumber_le_packingNumber δ K))
  by_contra h
  push_neg at h
  have hbound : ∀ S : Finset X, (↑S : Set X) ⊆ K →
      Metric.IsSeparated (δ : ℝ≥0∞) (↑S : Set X) → S.card ≤ M := by
    intro S hSK hsep
    exact h S hSK hsep
  have hpackle := HaarQuarter.TheoremD.packingNumber_le_of_finset_bound K δ M hbound
  exact (not_le_of_gt hpack) hpackle

end BrownianSharp.AlignmentAuditLifting
