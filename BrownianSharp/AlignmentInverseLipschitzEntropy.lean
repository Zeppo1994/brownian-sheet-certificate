import BrownianSharp.AlignmentIsometricEntropy

/-! Entropy lower bounds for maps with a controlled inverse distance,
including the factor two required by arbitrary ambient cover centers. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentInverseLipschitzEntropy
open Metric

theorem external_cover_le_of_inverse_distance
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Function.Injective f) (L : ℝ≥0)
    (hL : ∀ x y, dist x y ≤ (L:ℝ)*dist (f x) (f y))
    (K : Set X) (ρ : ℝ≥0) :
    externalCoveringNumber (L*(2*ρ)) K ≤ externalCoveringNumber ρ (f '' K) := by
  have hinternal : externalCoveringNumber (L*(2*ρ)) K ≤ coveringNumber (2*ρ) (f '' K) := by
    unfold coveringNumber
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    apply le_iInf
    intro hcover
    have hpull : IsCover (L*(2*ρ)) K (f ⁻¹' C) := by
      intro x hx
      obtain ⟨y,hy,hnear⟩ := hcover (Set.mem_image_of_mem f hx)
      obtain ⟨x',hx',rfl⟩ := hC hy
      refine ⟨x',hy,?_⟩
      change edist (f x) (f x') ≤ (2*ρ:ℝ≥0) at hnear
      change edist x x' ≤ (L*(2*ρ):ℝ≥0)
      rw [edist_dist] at hnear ⊢
      apply ENNReal.ofReal_le_coe.mpr
      have hn : dist (f x) (f x') ≤ (2*ρ:ℝ≥0) := ENNReal.ofReal_le_coe.mp hnear
      have hh := (hL x x').trans (mul_le_mul_of_nonneg_left hn L.property)
      simpa using hh
    have hcard : (f ⁻¹' C).encard = C.encard :=
      Set.encard_preimage_of_injective_subset_range hf
        (hC.trans (Set.image_subset_range f K))
    exact (hpull.externalCoveringNumber_le_encard).trans_eq hcard
  exact hinternal.trans (coveringNumber_two_mul_le_externalCoveringNumber ρ (f '' K))

theorem entropy_lower_of_inverse_distance
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Function.Injective f) (L : ℝ≥0) (hLpos : 0 < L)
    (hL : ∀ x y, dist x y ≤ (L:ℝ)*dist (f x) (f y))
    (K : Set X) (k : ℕ) (E : ℝ)
    (hE : ENNReal.ofReal E ≤ HaarQuarter.TheoremD.entropyNumber k K) :
    ENNReal.ofReal (E/(2*(L:ℝ))) ≤ HaarQuarter.TheoremD.entropyNumber k (f '' K) := by
  unfold HaarQuarter.TheoremD.entropyNumber at *
  apply le_sInf
  rintro q ⟨ρ,rfl,hcover⟩
  have hc : externalCoveringNumber (L*(2*ρ)) K ≤ ((2^(k-1):ℕ):ℕ∞) :=
    (external_cover_le_of_inverse_distance f hf L hL K ρ).trans hcover
  have hi := hE.trans (sInf_le (show
      (L*(2*ρ):ℝ≥0∞) ∈ {r : ℝ≥0∞ | ∃ δ : ℝ≥0,
        r = δ ∧ externalCoveringNumber δ K ≤ ((2^(k-1):ℕ):ℕ∞)} from
      ⟨L*(2*ρ),rfl,hc⟩))
  apply ENNReal.ofReal_le_coe.mpr
  apply (div_le_iff₀ (by exact mul_pos (by norm_num) hLpos)).mpr
  have hreal := ENNReal.ofReal_le_coe.mp hi
  norm_num only [NNReal.coe_mul, NNReal.coe_ofNat] at hreal
  nlinarith

end BrownianSharp.AlignmentInverseLipschitzEntropy
