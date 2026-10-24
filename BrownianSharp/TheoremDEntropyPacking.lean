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

/-- A finite separated subset larger than the allowed cover cardinality cannot
be covered at any radius below half its separation. The covering centers may
lie anywhere in the ambient pseudo-emetric space. -/
theorem no_small_cover_of_finite_packing
    (k : ℕ) (K : Set X) (S : Finset X) (δ : ℝ≥0)
    (hSK : (S : Set X) ⊆ K)
    (hsep : Metric.IsSeparated (δ : ℝ≥0∞) (S : Set X))
    (hlarge : 2 ^ (k - 1) < S.card) :
    ∀ ρ : ℝ≥0, ρ < δ / 2 →
      ¬ Metric.externalCoveringNumber ρ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  intro ρ hρ hcover
  have hρR : (ρ : ℝ) < (δ / 2 : ℝ) := by exact_mod_cast hρ
  have h2R : 2 * (ρ : ℝ) < (δ : ℝ) := by nlinarith
  have h2ρδ : (2 * ρ : ℝ≥0) ≤ δ := by exact_mod_cast h2R.le
  have hsep' : Metric.IsSeparated ((2 * ρ : ℝ≥0) : ℝ≥0∞) (S : Set X) :=
    hsep.anti (by exact_mod_cast h2ρδ)
  have hpack : (S : Set X).encard ≤ Metric.packingNumber (2 * ρ) K :=
    hsep'.encard_le_packingNumber hSK
  have hcmp : Metric.packingNumber (2 * ρ) K ≤ Metric.externalCoveringNumber ρ K :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber ρ K
  have hcard : (S : Set X).encard = S.card := by simp
  have hlarge' : ((2 ^ (k - 1) : ℕ) : ℕ∞) < (S.card : ℕ∞) := by
    exact_mod_cast hlarge
  rw [hcard] at hpack
  exact (not_le_of_gt hlarge') (hpack.trans (hcmp.trans hcover))

/-- The packing obstruction gives the sharp half-separation lower bound for
the dyadic entropy number. If there is no admissible covering radius, the
infimum is `∞` and the same proof applies vacuously through `le_sInf`. -/
theorem entropyNumber_ge_half_of_finite_packing
    (k : ℕ) (K : Set X) (S : Finset X) (δ : ℝ≥0)
    (hSK : (S : Set X) ⊆ K)
    (hsep : Metric.IsSeparated (δ : ℝ≥0∞) (S : Set X))
    (hlarge : 2 ^ (k - 1) < S.card) :
    (δ / 2 : ℝ≥0∞) ≤ entropyNumber k K := by
  apply le_sInf
  rintro r ⟨ρ, rfl, hcover⟩
  have hρ : δ / 2 ≤ ρ := by
    by_contra hnot
    exact (no_small_cover_of_finite_packing k K S δ hSK hsep hlarge ρ
      (lt_of_not_ge hnot)) hcover
  exact_mod_cast hρ

/-- A finite separated code transports to any isometric ambient realization
without changing its cardinality or its separation radius. -/
theorem finite_packing_image_isometry
    {X Y : Type*} [EMetricSpace X] [PseudoEMetricSpace Y]
    (f : X → Y) (hf : Isometry f) (K : Set X) (S : Finset X) (δ : ℝ≥0)
    (hSK : (S : Set X) ⊆ K)
    (hsep : Metric.IsSeparated (δ : ℝ≥0∞) (S : Set X)) :
    ∃ T : Finset Y, (T : Set Y) ⊆ f '' K ∧
      Metric.IsSeparated (δ : ℝ≥0∞) (T : Set Y) ∧ T.card = S.card := by
  classical
  refine ⟨S.image f, ?_, ?_, Finset.card_image_of_injective S hf.injective⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact ⟨x, hSK hx, rfl⟩
  · intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro h
      subst b
      exact hxy rfl
    rw [hf.edist_eq]
    exact hsep ha hb hab

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

/-- A finite separated-family bound gives an actual ambient-center cover and
therefore an upper bound on the dyadic entropy number. -/
theorem entropyNumber_le_of_finset_packing_bound
    {X : Type*} [PseudoEMetricSpace X] (K : Set X) (δ : ℝ≥0) (k : ℕ)
    (hfinite : ∀ S : Finset X, (S : Set X) ⊆ K →
      Metric.IsSeparated (δ : ℝ≥0∞) (S : Set X) → S.card ≤ 2 ^ (k - 1)) :
    entropyNumber k K ≤ (δ : ℝ≥0∞) := by
  have hp := packingNumber_le_of_finset_bound K δ (2 ^ (k - 1)) hfinite
  have hcover : Metric.externalCoveringNumber δ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) :=
    (Metric.externalCoveringNumber_le_coveringNumber δ K).trans
      ((Metric.coveringNumber_le_packingNumber δ K).trans hp)
  exact sInf_le ⟨δ, rfl, hcover⟩

end HaarQuarter.TheoremD
