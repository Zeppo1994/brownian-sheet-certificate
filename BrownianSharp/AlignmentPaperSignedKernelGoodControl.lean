import BrownianSharp.AlignmentPaperSignedKernelBadSeries

/-! Pointwise and L2 control of the actual mean-replacement good part. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperSignedKernelGoodControl
open BrownianSharp.AlignmentPaperSignedKernelBadSeries
open BrownianSharp.External.WeakCZ

theorem goodPart_eq_average_of_mem {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ)
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    {i : I} {x : UnitAddCircle} (hx : x ∈ E i) :
    goodPart μ E f x = ⨍ y in E i, f y ∂μ := by
  classical
  have hsum : (∑' j, badPiece μ (E j) f x) = badPiece μ (E i) f x := by
    apply tsum_eq_single i
    intro j hji
    have hxj : x ∉ E j := fun hxj => (Set.disjoint_left.mp (hdisj hji)) hxj hx
    simp [badPiece,hxj]
  unfold goodPart badPieceSeries
  rw [hsum]
  simp [badPiece,hx]

theorem goodPart_eq_self_of_notMem_iUnion {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ) {x : UnitAddCircle} (hx : x ∉ ⋃ i, E i) :
    goodPart μ E f x = f x := by
  have hzero : ∀ i, badPiece μ (E i) f x = 0 := by
    intro i
    have hxi : x ∉ E i := fun h => hx (mem_iUnion.mpr ⟨i,h⟩)
    simp [badPiece,hxi]
  simp only [goodPart,badPieceSeries,hzero,tsum_zero,sub_zero]

theorem ae_goodPart_norm_le {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ)
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    {C : ℝ} (havg : ∀ i, ‖⨍ y in E i, f y ∂μ‖ ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ ⋃ i, E i → ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖goodPart μ E f x‖ ≤ C := by
  filter_upwards [hout] with x hxout
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [goodPart_eq_average_of_mem μ E f hdisj hi]
    exact havg i
  · rw [goodPart_eq_self_of_notMem_iUnion μ E f hx]
    exact hxout hx

theorem goodPart_memLp_two_of_average_bounds {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) {C : ℝ}
    (havg : ∀ i, ‖⨍ y in E i, f y ∂μ‖ ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ ⋃ i, E i → ‖f x‖ ≤ C) :
    MemLp (goodPart μ E f) 2 μ :=
  MemLp.of_bound (goodPart_aestronglyMeasurable μ E f hE hdisj hf) C
    (ae_goodPart_norm_le μ E f hdisj havg hout)

theorem goodPart_square_moment_le {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) {C : ℝ} (hC : 0 ≤ C)
    (havg : ∀ i, ‖⨍ y in E i, f y ∂μ‖ ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ ⋃ i, E i → ‖f x‖ ≤ C) :
    (∫⁻ x, ENNReal.ofReal (‖goodPart μ E f x‖^2) ∂μ) ≤
      ENNReal.ofReal (3*C) * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hnorm := ae_goodPart_norm_le μ E f hdisj havg hout
  have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal (‖goodPart μ E f x‖^2) ≤
      ENNReal.ofReal C * ‖goodPart μ E f x‖ₑ := by
    filter_upwards [hnorm] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg (goodPart μ E f x)]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal C * ‖goodPart μ E f x‖ₑ ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal C * ∫⁻ x, ‖goodPart μ E f x‖ₑ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (3 * ∫⁻ x, ‖f x‖ₑ ∂μ) := by
      gcongr
      exact goodPart_lintegral_enorm_le_three μ E f hE hdisj hf
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
      ring

end BrownianSharp.AlignmentPaperSignedKernelGoodControl
