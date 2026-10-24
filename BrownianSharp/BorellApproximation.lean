import BrownianSharp.BorellInfinity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth compact set approximations used in Borell's heat proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace BrownianSharp
open Concentration

/-- A smooth compactly supported plateau between a compact set and any
positive metric neighbourhood. -/
theorem exists_borell_smooth_bump {κ : Type*} [Fintype κ]
    (K : Set (κ → ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : (κ → ℝ) → ℝ, ContDiff ℝ ∞ F ∧
      (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, F x = 1) ∧
      (∀ x, x ∉ Metric.thickening ε K → F x = 0) ∧
      HasCompactSupport F := by
  obtain ⟨F, hF, hFrange, hFsupp, hFone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      Metric.isOpen_thickening hK.isClosed (Metric.self_subset_thickening hε K)
  refine ⟨F, hF, fun x => hFrange (Set.mem_range_self x),
    fun x hx => (hFone x).mp hx, ?_, ?_⟩
  · intro x hx
    exact Function.notMem_support.mp (by simpa only [hFsupp] using hx)
  · apply hK.cthickening.of_isClosed_subset (isClosed_tsupport F)
    simpa only [tsupport, hFsupp] using Metric.closure_thickening_subset_cthickening ε K

theorem weightedMinkowski_eq_image {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b : ℝ) (K L : Set E) :
    weightedMinkowski a K b L =
      (fun xy : E × E => a • xy.1 + b • xy.2) '' (K ×ˢ L) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

theorem isCompact_weightedMinkowski {κ : Type*} [Fintype κ]
    (a b : ℝ) {K L : Set (κ → ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (weightedMinkowski a K b L) := by
  rw [weightedMinkowski_eq_image]
  exact (hK.prod hL).image (by fun_prop)

theorem weightedMinkowski_thickening_subset {κ : Type*} [Fintype κ]
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (K L : Set (κ → ℝ)) :
    weightedMinkowski a (Metric.thickening ε K) b (Metric.thickening ε L) ⊆
      Metric.thickening ε (weightedMinkowski a K b L) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨k, hk, hxk⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨l, hl, hyl⟩ := Metric.mem_thickening_iff.mp hy
  apply Metric.mem_thickening_iff.mpr
  refine ⟨a • k + b • l, ⟨k, hk, l, hl, rfl⟩, ?_⟩
  calc
    dist (a • x + b • y) (a • k + b • l) = ‖a • (x-k) + b • (y-l)‖ := by
      rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖a • (x-k)‖ + ‖b • (y-l)‖ := norm_add_le _ _
    _ = a * dist x k + b * dist y l := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, dist_eq_norm]
    _ < a * ε + b * ε := add_lt_add (mul_lt_mul_of_pos_left hxk ha)
      (mul_lt_mul_of_pos_left hyl hb)
    _ = ε := by rw [← add_mul, hab, one_mul]

/-- The comparison plateau equals one wherever both input plateaus can be
nonzero, and vanishes outside a twice-enlarged weighted compact sum. -/
theorem exists_borell_comparison_bump {κ : Type*} [Fintype κ]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (K L : Set (κ → ℝ)) (hK : IsCompact K) (hL : IsCompact L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : (κ → ℝ) → ℝ, ContDiff ℝ ∞ H ∧
      (∀ z, H z ∈ Set.Icc (0 : ℝ) 1) ∧ HasCompactSupport H ∧
      (∀ x ∈ Metric.thickening ε K, ∀ y ∈ Metric.thickening ε L,
        H (a • x + b • y) = 1) ∧
      (∀ z, z ∉ Metric.cthickening (2 * ε) (weightedMinkowski a K b L) → H z = 0) := by
  let C := weightedMinkowski a K b L
  have hC : IsCompact C := isCompact_weightedMinkowski a b hK hL
  obtain ⟨H, hHs, hHr, hHone, hHzero, hHc⟩ :=
    exists_borell_smooth_bump (Metric.cthickening ε C) hC.cthickening hε
  refine ⟨H, hHs, hHr, hHc, ?_, ?_⟩
  · intro x hx y hy
    apply hHone
    apply Metric.thickening_subset_cthickening ε C
    exact weightedMinkowski_thickening_subset ha hb hab K L ⟨x, hx, y, hy, rfl⟩
  · intro z hz
    apply hHzero
    intro hzin
    apply hz
    have hm := Metric.thickening_cthickening_subset ε hε.le C hzin
    exact Metric.thickening_subset_cthickening (2 * ε) C (by simpa [two_mul] using hm)

/-- Affine regularizations stay in the prescribed probability interval. -/
theorem borell_regularization_mem_Icc {F : ℝ} (hF : F ∈ Set.Icc (0 : ℝ) 1)
    {δ α : ℝ} (hδα : δ ≤ α) : δ + (α - δ) * F ∈ Set.Icc δ α := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hδα) hF.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hδα) (sub_nonneg.mpr hF.2)]

/-- The smooth compact approximations satisfy the actual initial two-point
quantile inequality. Only the elementary endpoint inequalities are required. -/
theorem borell_regularization_initial {κ : Type*} [Fintype κ]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (K L : Set (κ → ℝ)) (ε : ℝ)
    (F G H : (κ → ℝ) → ℝ)
    (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ x, G x ∈ Set.Icc (0 : ℝ) 1)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (hFzero : ∀ x, x ∉ Metric.thickening ε K → F x = 0)
    (hGzero : ∀ y, y ∉ Metric.thickening ε L → G y = 0)
    (hHone : ∀ x ∈ Metric.thickening ε K, ∀ y ∈ Metric.thickening ε L,
      H (a • x + b • y) = 1)
    {δ α β : ℝ} (hδ : 0 < δ) (hα : α < 1) (hδα : δ ≤ α)
    (hβ : 0 < β) (hβα : β ≤ α)
    (hbase1 : a * standardGaussianQuantile δ + b * standardGaussianQuantile α ≤
      standardGaussianQuantile β)
    (hbase2 : a * standardGaussianQuantile α + b * standardGaussianQuantile δ ≤
      standardGaussianQuantile β) :
    ∀ x y, a * standardGaussianQuantile (δ + (α-δ)*F x) +
      b * standardGaussianQuantile (δ + (α-δ)*G y) ≤
        standardGaussianQuantile (β + (α-β)*H (a • x + b • y)) := by
  intro x y
  have hFr := borell_regularization_mem_Icc (hF x) hδα
  have hGr := borell_regularization_mem_Icc (hG y) hδα
  have hHr := borell_regularization_mem_Icc (hH (a • x + b • y)) hβα
  have hδ1 : δ < 1 := hδα.trans_lt hα
  have hα0 : 0 < α := hδ.trans_le hδα
  have hβ1 : β < 1 := hβα.trans_lt hα
  have hFup := gaussianQuantile_mono_Ioo (hδ.trans_le hFr.1) (hFr.2.trans_lt hα)
    hα0 hα hFr.2
  have hGup := gaussianQuantile_mono_Ioo (hδ.trans_le hGr.1) (hGr.2.trans_lt hα)
    hα0 hα hGr.2
  have hHlo := gaussianQuantile_mono_Ioo hβ hβ1 (hβ.trans_le hHr.1)
    (hHr.2.trans_lt hα) hHr.1
  by_cases hx : x ∈ Metric.thickening ε K
  · by_cases hy : y ∈ Metric.thickening ε L
    · rw [hHone x hx y hy]
      have heq : β + (α-β)*1 = α := by ring
      rw [heq]
      have hFu := mul_le_mul_of_nonneg_left hFup ha.le
      have hGu := mul_le_mul_of_nonneg_left hGup hb.le
      calc
        _ ≤ a * standardGaussianQuantile α + b * standardGaussianQuantile α := add_le_add hFu hGu
        _ = _ := by rw [← add_mul, hab, one_mul]
    · rw [hGzero y hy, mul_zero, add_zero]
      have hFu := mul_le_mul_of_nonneg_left hFup ha.le
      linarith
  · rw [hFzero x hx, mul_zero, add_zero]
    have hGu := mul_le_mul_of_nonneg_left hGup hb.le
    linarith

end BrownianSharp
