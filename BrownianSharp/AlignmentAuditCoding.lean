import BrownianSharp.SharpCertified
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite coding lower bounds from external entropy

This module formalizes finite encoder/decoder approximation in the ambient
metric space. Decoder outputs are unrestricted ambient reconstruction centers.
-/

open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentAuditCoding

variable {X : Type*} [PseudoEMetricSpace X] [Nonempty X]

/-- A finite alphabet encoder and ambient-space decoder approximate every
point of `K` within `ε`. -/
def UniformCode (K : Set X) (ε : ℝ≥0) (ι : Type*) [Fintype ι] : Prop :=
  ∃ enc : {x // x ∈ K} → ι, ∃ dec : ι → X,
    ∀ x : {x // x ∈ K}, edist x.val (dec (enc x)) ≤ ε

/-- Finite codebooks and finite external covers are exactly the same object,
with no restriction that reconstruction centers lie in the target set. -/
theorem uniformCode_iff_finiteExternalCover
    (K : Set X) (ε : ℝ≥0) (ι : Type*) [Fintype ι] :
    UniformCode K ε ι ↔
      ∃ C : Set X, C.Finite ∧ Metric.IsCover ε K C ∧
        C.encard ≤ Fintype.card ι := by
  classical
  constructor
  · rintro ⟨enc, dec, happrox⟩
    let C : Set X := Set.range dec
    refine ⟨C, Set.finite_range dec, ?_, ?_⟩
    · intro x hx
      refine ⟨dec (enc ⟨x, hx⟩), ⟨enc ⟨x, hx⟩, rfl⟩, ?_⟩
      exact happrox ⟨x, hx⟩
    · change ENat.card (↥(Set.range dec)) ≤ Fintype.card ι
      rw [ENat.card_eq_coe_natCard]
      rw [← Nat.card_eq_fintype_card (α := ι)]
      exact_mod_cast Finite.card_range_le dec
  · rintro ⟨C, hCfin, hcover, hcard⟩
    let α := {x // x ∈ C}
    letI : Fintype α := hCfin.fintype
    have hα : Fintype.card α ≤ Fintype.card ι := by
      have henc : C.encard = Fintype.card α := by
        simpa [α] using hCfin.encard_eq_coe_toFinset_card
      have hcard' : (Fintype.card α : ℕ∞) ≤ Fintype.card ι := by
        rw [← henc]
        exact hcard
      exact_mod_cast hcard'
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hα
    let dec : ι → X := fun i =>
      if hi : ∃ y : α, e y = i then (Classical.choose hi).val else Classical.choice ‹Nonempty X›
    let enc : {x // x ∈ K} → ι := fun x =>
      e ⟨Classical.choose (hcover x.property),
        (Classical.choose_spec (hcover x.property)).1⟩
    refine ⟨enc, dec, ?_⟩
    intro x
    let y := Classical.choose (hcover x.property)
    have hy : y ∈ C := (Classical.choose_spec (hcover x.property)).1
    have hdist : edist x.val y ≤ ε := (Classical.choose_spec (hcover x.property)).2
    have hi : ∃ z : α, e z = enc x := ⟨⟨y, hy⟩, rfl⟩
    have hdecode : dec (enc x) = y := by
      have hpre : Classical.choose hi = (⟨y, hy⟩ : α) := by
        apply e.injective
        exact Classical.choose_spec hi
      simp [dec, hi, hpre]
    rw [hdecode]
    exact hdist

/-- A `B`-bit code gives an external cover by at most `2^B` arbitrary
ambient centers. -/
theorem externalCover_of_bitCode
    (K : Set X) (ε : ℝ≥0) (B : ℕ)
    (hcode : UniformCode K ε (Fin (2 ^ B))) :
    Metric.externalCoveringNumber ε K ≤ ((2 ^ B : ℕ) : ℕ∞) := by
  obtain ⟨C, hCfin, hcover, hcard⟩ :=
    (uniformCode_iff_finiteExternalCover K ε (Fin (2 ^ B))).mp hcode
  exact le_trans (Metric.IsCover.externalCoveringNumber_le_encard hcover) (by
    simpa using hcard)

/-- If a `B`-bit code approximates a set, its `(B+1)`-st dyadic entropy
number is at most its worst-case reconstruction error. -/
theorem entropyNumber_le_of_bitCode
    (K : Set X) (ε : ℝ≥0) (B : ℕ)
    (hcode : UniformCode K ε (Fin (2 ^ B))) :
    HaarQuarter.TheoremD.entropyNumber (B + 1) K ≤ (ε : ℝ≥0∞) := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply sInf_le
  refine ⟨ε, rfl, ?_⟩
  simpa [Nat.add_sub_cancel] using externalCover_of_bitCode K ε B hcode


/-- If the external covering number of a target class is at least `2^n`, a
uniform encoder/decoder with `B` bits must have `n ≤ B`. This applies to
function classes by taking `X` to be their ambient function space and allowing
decoder outputs anywhere in that space. -/
theorem bitCount_ge_of_externalCover_lower
    (K : Set X) (ε : ℝ≥0) (n B : ℕ)
    (hlower : ((2 ^ n : ℕ) : ℕ∞) ≤ Metric.externalCoveringNumber ε K)
    (hcode : UniformCode K ε (Fin (2 ^ B))) : n ≤ B := by
  have hupper := externalCover_of_bitCode K ε B hcode
  have hpowENN : ((2 ^ n : ℕ) : ℕ∞) ≤ (2 ^ B : ℕ) := hlower.trans hupper
  have hpow : 2 ^ n ≤ 2 ^ B := by exact_mod_cast hpowENN
  exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow

/-- The certified Cameron--Martin lower entropy rate forces every finite
uniform code of the `d`-dimensional anchored unit ball to have error at least
the entropy lower bound at its bit index. -/
theorem cameronMartin_bitCode_error_lower
    {d B : ℕ} (hd : 2 ≤ d) (hB : 2 ≤ B + 1)
    (ε : ℝ≥0) (hcode : UniformCode
      (CameronMartin.KdUnitCube d) ε (Fin (2 ^ B))) :
    ∃ c : ℝ, 0 < c ∧
      ¬ (ε : ℝ) < c * BrownianSharp.cmIndexRate d (B + 1) := by
  obtain ⟨c₀, hc₀, hlower⟩ := BrownianSharp.cameronMartinEntropyLower_certified hd
  have hrate := hlower (B + 1) hB
  have hentropy := entropyNumber_le_of_bitCode
    (CameronMartin.KdUnitCube d) ε B hcode
  refine ⟨c₀, hc₀, ?_⟩
  intro hε
  have hratepos : 0 < BrownianSharp.cmIndexRate d (B + 1) := by
    have hkR : 1 < ((B + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < B + 1)
    have hlog : 0 < Real.log ((B + 1 : ℕ) : ℝ) := Real.log_pos hkR
    have hpow : 0 < (Real.log ((B + 1 : ℕ) : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
      Real.rpow_pos_of_pos hlog _
    have hkinv : 0 < ((B + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := by positivity
    simpa [BrownianSharp.cmIndexRate, BrownianSharp.logarithmicIndexRate] using
      mul_pos hkinv hpow
  have hnonneg : 0 ≤ c₀ * BrownianSharp.cmIndexRate d (B + 1) :=
    le_of_lt (mul_pos hc₀ hratepos)
  have hε' : (ε : ℝ≥0∞) <
      ENNReal.ofReal (c₀ * BrownianSharp.cmIndexRate d (B + 1)) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]
    exact_mod_cast hε
  exact (not_lt_of_ge (le_trans hrate hentropy)) hε'

end BrownianSharp.AlignmentAuditCoding
