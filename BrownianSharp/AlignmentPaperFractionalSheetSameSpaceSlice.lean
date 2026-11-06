import BrownianSharp.AlignmentPaperFractionalSheetSlice

/-! Construct the minimum-Hurst fractional sheet on the original probability
space by restricting the actual path. The restricted field is a genuine
fractional-sheet realization, and its uniform norm is dominated pathwise by
the original field's norm. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperFractionalSheetSlice
open BrownianSharp.Latest
open HaarQuarter

/-- The actual restriction of an anisotropic sheet to selected coordinates,
with all other coordinates frozen at one, as a sheet on the same space. -/
def sameSpaceMinimumCoordinateSheet
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hh : 0 < h ∧ h < 1) (j : Fin ν ↪ Fin d)
    (hactive : ∀ a, B.H (j a) = h) :
    FractionalBrownianSheetOnCube ν Ω P := by
  let slice := minimumCoordinateSlice j
  let F := restrictedSheetPath B slice
  have hF : Measurable F := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro x
    convert (ContinuousMap.measurable_eval (slice x)).comp B.measurable_path using 1
    rfl
  refine {
    H := fun _ => h
    hH := fun _ => hh
    path := F
    measurable_path := hF
    gaussian := ?_
    mean_zero := ?_
    covariance := ?_ }
  · change IsGaussianProcess
      ((fun x : BrownianCubeAnchor d => fun ω => B.path ω x) ∘ slice) P
    exact B.gaussian.comp_right slice
  · intro x
    exact B.mean_zero (slice x)
  · intro x y
    calc
      cov[fun ω => F ω x, fun ω => F ω y; P] =
          fractionalSheetCovariance B.H (slice x) (slice y) := by
        rw [show (fun ω => F ω x) = fun ω => B.path ω (slice x) by rfl,
          show (fun ω => F ω y) = fun ω => B.path ω (slice y) by rfl,
          B.covariance]
      _ = fractionalSheetCovariance (fun _ : Fin ν => h) x y :=
        fractionalSheetCovariance_minimumCoordinateSlice B.H h
          (fun i => (B.hH i).1) j hactive x y

theorem sameSpaceMinimumCoordinateSheet_path_norm_le
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hh : 0 < h ∧ h < 1) (j : Fin ν ↪ Fin d)
    (hactive : ∀ a, B.H (j a) = h) (ω : Ω) :
    ‖(sameSpaceMinimumCoordinateSheet B h hh j hactive).path ω‖ ≤
      ‖B.path ω‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  change ‖B.path ω (minimumCoordinateSlice j x)‖ ≤ ‖B.path ω‖
  exact ContinuousMap.norm_coe_le_norm (B.path ω) (minimumCoordinateSlice j x)

theorem sameSpaceMinimumCoordinateSheet_smallBall_event_subset
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hh : 0 < h ∧ h < 1) (j : Fin ν ↪ Fin d)
    (hactive : ∀ a, B.H (j a) = h) (ε : ℝ) :
    {ω | ‖B.path ω‖ ≤ ε} ⊆
      {ω | ‖(sameSpaceMinimumCoordinateSheet B h hh j hactive).path ω‖ ≤ ε} := by
  intro ω hω
  exact (sameSpaceMinimumCoordinateSheet_path_norm_le B h hh j hactive ω).trans hω

/-- The restricted small-ball probability is at least the original one. -/
theorem sameSpaceMinimumCoordinateSheet_smallBall_probability_ge
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hh : 0 < h ∧ h < 1) (j : Fin ν ↪ Fin d)
    (hactive : ∀ a, B.H (j a) = h) (ε : ℝ) :
    P.real {ω | ‖B.path ω‖ ≤ ε} ≤
      P.real {ω | ‖(sameSpaceMinimumCoordinateSheet B h hh j hactive).path ω‖ ≤ ε} := by
  apply measureReal_mono
    (sameSpaceMinimumCoordinateSheet_smallBall_event_subset B h hh j hactive ε)

theorem minimumMultiplicity_hurst_mem_unitInterval
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hm : minimumMultiplicity B.H h ν) (hν : 1 ≤ ν) :
    0 < h ∧ h < 1 := by
  have hcard : 0 < (Finset.univ.filter (fun i : Fin d => B.H i = h)).card := by
    rw [hm.2]
    omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hcard
  have heq : B.H i = h := (Finset.mem_filter.mp hi).2
  rw [← heq]
  exact ⟨(B.hH i).1,(B.hH i).2⟩

/-- Every minimum-multiplicity profile yields an actual restricted sheet on
the same probability space, together with the pathwise norm and small-ball
probability comparisons. -/
theorem exists_sameSpace_minimumMultiplicity_slice
    {d ν : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (B : FractionalBrownianSheetOnCube d Ω P) (h : ℝ)
    (hm : minimumMultiplicity B.H h ν) (hν : 1 ≤ ν) :
    ∃ j : Fin ν ↪ Fin d,
      (∀ a, B.H (j a) = h) ∧
      ∃ Bν : FractionalBrownianSheetOnCube ν Ω P,
        Bν.H = (fun _ => h) ∧
        Bν.path = restrictedSheetPath B (minimumCoordinateSlice j) ∧
        (∀ ω, ‖Bν.path ω‖ ≤ ‖B.path ω‖) ∧
        (∀ ε : ℝ, P.real {ω | ‖B.path ω‖ ≤ ε} ≤
          P.real {ω | ‖Bν.path ω‖ ≤ ε}) := by
  have hcard : Fintype.card {i : Fin d // B.H i = h} = ν := by
    rw [Fintype.card_subtype]
    simpa using hm.2
  have heq : Fintype.card (Fin ν) =
      Fintype.card {i : Fin d // B.H i = h} := (Fintype.card_fin ν).trans hcard.symm
  let e : Fin ν ≃ {i : Fin d // B.H i = h} := Fintype.equivOfCardEq heq
  let j : Fin ν ↪ Fin d :=
    ⟨fun a => (e a).val, fun a b hab => e.injective (Subtype.ext hab)⟩
  have hactive : ∀ a, B.H (j a) = h := fun a => (e a).property
  refine ⟨j,hactive,?_⟩
  have hh := minimumMultiplicity_hurst_mem_unitInterval B h hm hν
  let Bν := sameSpaceMinimumCoordinateSheet B h hh j hactive
  refine ⟨Bν,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro ω
    exact sameSpaceMinimumCoordinateSheet_path_norm_le B h hh j hactive ω
  · intro ε
    exact sameSpaceMinimumCoordinateSheet_smallBall_probability_ge
      B h hh j hactive ε

end BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice
