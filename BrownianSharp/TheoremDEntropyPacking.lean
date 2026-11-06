import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Packing obstruction for dyadic entropy numbers

This is the deterministic metric foundation for the entropy route to Theorem D.
The entropy number is the infimum, in `ℝ≥0∞`, of the radii at which the
external covering number is at most `2^(k-1)`. Using an extended nonnegative
real infimum makes the empty family of admissible covers unambiguous: its
infimum is `∞`.
-/

open Set
open scoped ENNReal NNReal

namespace HaarQuarter.TheoremD

variable {X : Type*} [PseudoEMetricSpace X]

/-- The `k`th dyadic entropy number of `K`, defined by ambient-center covers
using at most `2^(k-1)` balls. -/
noncomputable def entropyNumber (k : ℕ) (K : Set X) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ ρ : ℝ≥0, r = ρ ∧
    Metric.externalCoveringNumber ρ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞)}

end HaarQuarter.TheoremD

open Set
open scoped ENNReal NNReal

namespace HaarQuarter.TheoremD

/-- Bounding all finite separated families bounds the full packing number,
including the possibility of an infinite separated set. -/
theorem packingNumber_le_of_finset_bound
    {X : Type*} [PseudoEMetricSpace X] (K : Set X) (δ : ℝ≥0) (n : ℕ)
    (hfinite : ∀ S : Finset X, (S : Set X) ⊆ K →
      Metric.IsSeparated (δ : ℝ≥0∞) (S : Set X) → S.card ≤ n) :
    Metric.packingNumber δ K ≤ (n : ℕ∞) := by
  classical
  unfold Metric.packingNumber
  apply iSup_le
  intro C
  apply iSup_le
  intro hCK
  apply iSup_le
  intro hsep
  by_contra hn
  have hlt : (n : ℕ∞) < C.encard := lt_of_not_ge hn
  have hn1 : ((n + 1 : ℕ) : ℕ∞) ≤ C.encard := by
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hlt
  obtain ⟨S, hSC, hcard⟩ := Set.exists_subset_encard_eq hn1
  have hSfinite : S.Finite := Set.encard_ne_top_iff.mp (by rw [hcard]; exact ENat.natCast_ne_top _)
  have hSsep : Metric.IsSeparated (δ : ℝ≥0∞) (hSfinite.toFinset : Set X) := by
    change Metric.IsSeparated (δ : ℝ≥0∞) (hSfinite.toFinset : Set X)
    rw [hSfinite.coe_toFinset]
    exact hsep.mono hSC
  have hbound := hfinite hSfinite.toFinset (by simpa using hSC.trans hCK) hSsep
  have hcardNat : hSfinite.toFinset.card = n + 1 := by
    have h := hSfinite.encard_eq_coe_toFinset_card
    rw [hcard] at h
    exact_mod_cast h.symm
  omega

end HaarQuarter.TheoremD
