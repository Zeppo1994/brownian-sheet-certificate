import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.BrownianCubeSpan

/-! Restriction laws for fractional Brownian sheet paths, obtained from the
actual sheet covariance and the generic centered-Gaussian path-law theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open HaarQuarter

namespace BrownianSharp.AlignmentPaperFractionalSheetSlice

open BrownianSharp.AlignmentPaperGaussianFeatureBridge
open BrownianSharp.AlignmentGaussianRates

/-- Restrict a continuous sheet path along a continuous parameter map. -/
def restrictedSheetPath {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : FractionalBrownianSheetOnCube d Ω P)
    (slice : C(BrownianCubeAnchor ν, BrownianCubeAnchor d)) :
    Ω → C(BrownianCubeAnchor ν, ℝ) := fun ω =>
  ⟨fun x => B.path ω (slice x),
    (B.path ω).continuous.comp slice.continuous⟩

/-- Restrict a cube by retaining the coordinates in an injective list and
fixing every other coordinate at the normalized endpoint `1`. -/
def minimumCoordinateSlice {d ν : ℕ} (j : Fin ν ↪ Fin d) :
    C(BrownianCubeAnchor ν, BrownianCubeAnchor d) := by
  let v : BrownianCubeAnchor ν → Fin d → ℝ := fun x i =>
    if hi : ∃ a, j a = i then x.val (Classical.choose hi) else 1
  have hv : Continuous v := by
    apply continuous_pi
    intro i
    by_cases hi : ∃ a, j a = i
    · have hc : Continuous
          (fun x : BrownianCubeAnchor ν => x.val (Classical.choose hi)) :=
        (continuous_apply (Classical.choose hi)).comp continuous_subtype_val
      simpa [v, hi] using hc
    · simpa [v, hi] using continuous_const
  have hbound (x : BrownianCubeAnchor ν) (i : Fin d) : v x i ∈ Set.Icc (0:ℝ) 1 := by
    by_cases hi : ∃ a, j a = i
    · simpa [v, hi] using x.property (Classical.choose hi)
    · simp [v, hi]
  exact ⟨fun x => ⟨v x, hbound x⟩, hv.subtype_mk _⟩

@[simp] theorem minimumCoordinateSlice_apply_range {d ν : ℕ}
    (j : Fin ν ↪ Fin d) (x : BrownianCubeAnchor ν) (a : Fin ν) :
    (minimumCoordinateSlice j x).val (j a) = x.val a := by
  have hi : ∃ b, j b = j a := ⟨a, rfl⟩
  have hchoose : Classical.choose hi = a := j.injective (Classical.choose_spec hi)
  simp [minimumCoordinateSlice, hi, hchoose]

theorem minimumCoordinateSlice_apply_not_range {d ν : ℕ}
    (j : Fin ν ↪ Fin d) (x : BrownianCubeAnchor ν) (i : Fin d)
    (hi : ∀ a, j a ≠ i) :
    (minimumCoordinateSlice j x).val i = 1 := by
  have hnot : ¬ ∃ a, j a = i := by
    rintro ⟨a, ha⟩
    exact hi a ha
  simp [minimumCoordinateSlice, hnot]

/-- The normalized endpoint has unit fractional-coordinate variance for every
positive Hurst parameter. This is the factor contributed by frozen
coordinates in the covariance product. -/
theorem fractionalCoordinateCovariance_one_one {H : ℝ} (hH : 0 < H) :
    fractionalCoordinateCovariance H 1 1 = 1 := by
  unfold fractionalCoordinateCovariance
  have hpow : 0 < 2 * H := by positivity
  simp [Real.zero_rpow (ne_of_gt hpow)]

/-- Exact covariance-product identity for a coordinate slice: selected
coordinates have common Hurst parameter `h`, and all other coordinates are
fixed at `1`, where their variance factor is exactly one. -/
theorem fractionalSheetCovariance_minimumCoordinateSlice
    {d ν : ℕ} (H : Fin d → ℝ) (h : ℝ)
    (hH : ∀ i, 0 < H i) (j : Fin ν ↪ Fin d)
    (hactive : ∀ a, H (j a) = h)
    (x y : BrownianCubeAnchor ν) :
    fractionalSheetCovariance H (minimumCoordinateSlice j x)
        (minimumCoordinateSlice j y) =
      fractionalSheetCovariance (fun _ : Fin ν => h) x y := by
  classical
  let S : Finset (Fin d) := Finset.univ.image j
  let f : Fin d → ℝ := fun i => fractionalCoordinateCovariance (H i)
      ((minimumCoordinateSlice j x).val i) ((minimumCoordinateSlice j y).val i)
  have houtside : ∀ i ∈ Finset.univ \ S, f i = 1 := by
    intro i hi
    have hnot : ∀ a, j a ≠ i := by
      intro a ha
      have hmem : i ∈ S := by
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
      have hmem' : i ∈ Finset.univ \ S := hi
      exact (Finset.mem_sdiff.mp hmem').2 hmem
    change fractionalCoordinateCovariance (H i)
      ((minimumCoordinateSlice j x).val i) ((minimumCoordinateSlice j y).val i) = 1
    rw [minimumCoordinateSlice_apply_not_range j x i hnot,
      minimumCoordinateSlice_apply_not_range j y i hnot]
    exact fractionalCoordinateCovariance_one_one (hH i)
  have hactiveprod : ∏ i ∈ S, f i =
      ∏ a : Fin ν, fractionalCoordinateCovariance h (x.val a) (y.val a) := by
    rw [Finset.prod_image j.injective.injOn]
    apply Finset.prod_congr rfl
    intro a ha
    simp [f, hactive a, minimumCoordinateSlice_apply_range]
  have hwhole : ∏ i : Fin d, f i = ∏ i ∈ S, f i := by
    have hsplit := Finset.prod_sdiff (s₁ := S) (s₂ := Finset.univ)
      (Finset.subset_univ S) (f := f)
    have hzero : ∏ i ∈ Finset.univ \ S, f i = 1 :=
      Finset.prod_eq_one houtside
    calc
      ∏ i : Fin d, f i =
          (∏ i ∈ Finset.univ \ S, f i) * ∏ i ∈ S, f i := hsplit.symm
      _ = ∏ i ∈ S, f i := by rw [hzero]; simp
  rw [show fractionalSheetCovariance H (minimumCoordinateSlice j x)
      (minimumCoordinateSlice j y) = ∏ i : Fin d, f i by rfl,
    hwhole, hactiveprod]
  rfl

end BrownianSharp.AlignmentPaperFractionalSheetSlice
