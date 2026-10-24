import BrownianSharp.AlignmentGaussianMvNFullLineFiltration
import BrownianSharp.AlignmentAuditGaussianScalarClosure
import Mathlib.Tactic

/-! Actual one-sided fractional-sheet small-ball upper-log theorem, obtained
by instantiating the generic graded Gaussian closure with the concrete
two-sided MvN scalar filtrations. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentGaussianActualFractionalUpperLog

open BrownianSharp.AlignmentGaussianMvNFullLineFiltration
open BrownianSharp.AlignmentAuditGaussianScalarClosure
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.Latest
open HaarQuarter
open BrownianSharp.AlignmentFractionalTensorOperator

/-- The scalar MvN polynomial/Taylor filtrations discharge the hypotheses of
the abstract graded reverse theorem for every anisotropic fractional sheet. -/
theorem fractionalSheet_upperLog_of_actualMvN_scalar_filtrations
    {ν e : ℕ} (hν : 2 ≤ ν) (H : Fin (ν+e) → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ)
    (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ C₀ ε₀ : ℝ, 0 < C₀ ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube (ν+e) Ω P), B.H = H →
        ∀ ε, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} ∧
          -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) ≤
            C₀ * Latest.smallBallRate h⁻¹
              (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
  classical
  let d := ν+e
  let U : Fin d → ℕ → Submodule ℝ FullLineL2 := fun i n =>
    actualMvNFiltration (H i) (hH i).1 (hH i).2 n
  have hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n) := by
    intro i n
    exact actualMvNFiltration_finiteDimensional (H i) (hH i).1 (hH i).2 n
  have hnested : ∀ i n, U i n ≤ U i (n+1) := by
    intro i n
    exact actualMvNFiltration_mono (H i) (hH i).1 (hH i).2 n
  have hbase : ∀ i, Nonempty (GradeIndex (U i) 0) := by
    intro i
    exact actualMvNFiltration_grade_zero_nonempty (H i) (hH i).1 (hH i).2
  have hAexists : ∀ i, ∃ A : ℕ, 0 < A ∧ ∀ g,
      Fintype.card (GradeIndex (U i) g) ≤ A*2^g := by
    intro i
    exact actualMvNFiltration_grade_card_bound (H i) (hH i).1 (hH i).2
  choose A hApos hcard using hAexists
  have hCexists : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ n (t : UnitInterval),
      (letI : FiniteDimensional ℝ (U i n) := hfinite i n
       ‖normalizedAxis (H i) (hH i).1 (hH i).2 t -
          (U i n).starProjection (normalizedAxis (H i) (hH i).1 (hH i).2 t)‖^2 ≤
        C*((2:ℝ)^(-2*H i))^n) := by
    intro i
    exact normalizedAxis_actualMvN_projection_rate (H i) (hH i).1 (hH i).2
  choose C hCpos hres using hCexists
  have hC : ∀ i, 0 ≤ C i := fun i => le_of_lt (hCpos i)
  have hres' : ∀ (t : BrownianCubeAnchor d) i n,
      (letI : FiniteDimensional ℝ (U i n) := hfinite i n
       ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
          (U i n).starProjection
            (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖^2 ≤
        C i * (Real.rpow 2 (-(2*H i)))^n) := by
    intro t i n
    have hh := hres i n (cubeCoordinate i t)
    have hpow : (2:ℝ)^(-2*H i) = Real.rpow 2 (-(2*H i)) := by
      congr 1 <;> ring
    simpa [hpow] using hh
  have hh : 0 < h := by
    have hcardpos : 0 < (Finset.univ.filter (fun i : Fin d => H i = h)).card := by
      rw [hmin.2]
      omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hcardpos
    have hieq : H i = h := (Finset.mem_filter.mp hi).2
    rw [← hieq]
    exact (hH i).1
  let η := Real.sqrt (Real.rpow 2 (-2*h)/2)
  have hqpos : 0 < Real.rpow 2 (-2*h) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hqle : Real.rpow 2 (-2*h)/2 ≤ 1 := by
    have hq_lt : Real.rpow 2 (-2*h) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    have hqpos' : 0 ≤ Real.rpow 2 (-2*h) := le_of_lt hqpos
    linarith
  have hη : 0 < η := by
    dsimp [η]
    exact Real.sqrt_pos.2 (by positivity)
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact Real.sqrt_le_one.mpr hqle
  have hηsq : η^2 = Real.rpow 2 (-2*h)/2 := by
    dsimp [η]
    rw [Real.sq_sqrt]
    positivity
  exact fractionalSheet_upperLog_of_scalar_filtrations hν H hH h hmin
    U hfinite hnested hbase A C hApos hC hcard hres' η hη hη1 hηsq

/-- Dimension-free formulation matching the literal latest statement. The
minimum-multiplicity hypothesis itself forces `ν ≤ d`; writing `d=ν+(d-ν)`
then lets the graded closure split active and inactive coordinates. -/
theorem fractionalSheet_upperLog_of_actualMvN_scalar_filtrations_any_dimension
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ C₀ ε₀ : ℝ, 0 < C₀ ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (B : FractionalBrownianSheetOnCube d Ω P),
        B.H = H → ∀ ε, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} ∧
          -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) ≤
            C₀ * Latest.smallBallRate h⁻¹
              (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
  have hνd : ν ≤ d := by
    calc
      ν = (Finset.univ.filter (fun i : Fin d => H i = h)).card := hmin.2.symm
      _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
      _ = d := by simp
  obtain ⟨e,hdEq⟩ : ∃ e : ℕ, d = ν+e := ⟨d-ν, by omega⟩
  subst d
  exact fractionalSheet_upperLog_of_actualMvN_scalar_filtrations
    hν H hH h hmin

end BrownianSharp.AlignmentGaussianActualFractionalUpperLog
