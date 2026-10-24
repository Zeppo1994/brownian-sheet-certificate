import BrownianSharp.AlignmentGaussianAuditFrameProfile
import BrownianSharp.AlignmentFractionalSheetGradedFrame
import BrownianSharp.AlignmentGaussianGradedFeatureVariance
import BrownianSharp.AlignmentGaussianFractionalReverseClosure
import BrownianSharp.AlignmentUniformGeometricApproximation
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalPaddingPermutation
import BrownianSharp.AlignmentFractionalSheetMvNGram
import BrownianSharp.AlignmentFintypeIrrelevance
import Mathlib.Tactic

set_option maxHeartbeats 1000000

/-! Conditional composition of scalar whole-line source filtrations with the
actual fractional-sheet reverse. This file turns the concrete coordinate
profile estimates into the four uniform finite-frame hypotheses; only the
scalar filtration estimates themselves remain external inputs. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentAuditGaussianScalarClosure

open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentGaussianAuditFrameProfile
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalSheetGradedFrame
open BrownianSharp.AlignmentGaussianGradedFeatureVariance
open BrownianSharp.AlignmentGaussianFractionalReverseClosure
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentExponentialGradedReverseInversion
open BrownianSharp.Latest
open GaussianProjection
open HaarQuarter

private theorem audit_rpow_dyadic_rate_sq (β : ℝ) (N : ℕ) :
    (Real.rpow 2 (-β * (N : ℝ) / 2))^2 =
      (Real.rpow 2 (-β))^N := by
  calc
    (Real.rpow 2 (-β * (N : ℝ) / 2))^2 =
        Real.rpow 2 ((-β * (N : ℝ) / 2) * 2) := by
          calc
            _ = Real.rpow (Real.rpow 2 (-β * (N : ℝ) / 2)) (2:ℝ) :=
              (Real.rpow_natCast _ _).symm
            _ = _ := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)
              (-β*(N:ℝ)/2) 2).symm
    _ = Real.rpow 2 (-β * (N : ℝ)) := by congr 1 <;> ring
    _ = (Real.rpow 2 (-β))^N := by
      calc
        _ = Real.rpow (Real.rpow 2 (-β)) (N:ℝ) :=
          Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-β) (N:ℝ)
        _ = _ := Real.rpow_natCast _ _

/-- From coordinatewise finite nested source filtrations, their grade growth,
and geometric squared projection rates, obtain the actual sharp one-sided
fractional-sheet small-ball upper-log estimate. Uniform projection convergence
is derived here from the geometric rates, not assumed separately. -/
theorem fractionalSheet_upperLog_of_scalar_filtrations
    {ν e : ℕ} (hν : 2 ≤ ν) (H : Fin (ν+e) → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ)
    (hmin : Latest.minimumMultiplicity H h ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ FullLineL2)
    (hfinite : ∀ i m, FiniteDimensional ℝ ↥(U i m))
    (hnested : ∀ i m, U i m ≤ U i (m+1))
    (hbase : ∀ i, Nonempty (GradeIndex (U i) 0))
    (A : Fin (ν+e) → ℕ) (C : Fin (ν+e) → ℝ)
    (hApos : ∀ i, 0 < A i) (hC : ∀ i, 0 ≤ C i)
    (hcard : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i*2^g)
    (hres : ∀ (t : BrownianCubeAnchor (ν+e)) i m,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i m).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖^2 ≤
        C i * (Real.rpow 2 (-(2*H i)))^m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηsq : η^2 = Real.rpow 2 (-2*h)/2) :
    ∃ C₀ ε₀ : ℝ, 0 < C₀ ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube (ν+e) Ω P), B.H = H →
        ∀ ε, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} ∧
          -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) ≤
            C₀ * Latest.smallBallRate h⁻¹
              (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
  classical
  let d := ν+e
  let α : Fin d → ℝ := fun i => H i + 1/2
  let r : ℝ := h+1/2
  have hh : 0 < h := by
    unfold Latest.minimumMultiplicity at hmin
    have hcard0 : 0 < (Finset.univ.filter (fun i : Fin d => H i = h)).card := by
      rw [hmin.2]
      omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hcard0
    have hieq : H i = h := (Finset.mem_filter.mp hi).2
    rw [← hieq]
    exact (hH i).1
  have hr : 1/2 < r := by dsimp [r]; linarith
  have hqpos0 : 0 < Real.rpow 2 (-2*h) := Real.rpow_pos_of_pos (by norm_num) _
  have hqone0 : Real.rpow 2 (-2*h) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hmα : Latest.minimumMultiplicity α r ν := by
    unfold Latest.minimumMultiplicity at hmin ⊢
    constructor
    · intro i
      have hi := hmin.1 i
      dsimp [α,r]
      linarith
    · have hsets : Finset.univ.filter (fun i : Fin d => α i = r) =
          Finset.univ.filter (fun i : Fin d => H i = h) := by
        ext i
        simp [α,r]
      rw [hsets]
      exact hmin.2
  have hcardα : (minimumIndexSet α r).card = ν := by
    unfold Latest.minimumMultiplicity at hmα
    simpa [minimumIndexSet] using hmα.2
  let ep := minimumCoordinatePermutation α r hcardα
  let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j))/r
  have hw : ∀ j, 1 < w j := by
    intro j
    have hr0 : 0 < r := by dsimp [r]; linarith
    rw [one_lt_div₀ hr0]
    exact minimumCoordinatePermutation_inactive_lt α r hcardα hmα.1 j
  let q : Fin d → ℝ := fun i => Real.rpow 2 (-(2*H i))
  have hqpos : ∀ i, 0 < q i := by
    intro i
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hqone : ∀ i, q i < 1 := by
    intro i
    dsimp [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith [(hH i).1]
  let err : Fin d → ℕ → BrownianCubeAnchor d → ℝ := fun i m t =>
    ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
      (U i m).starProjection
        (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖
  have herr0 : ∀ i m t, 0 ≤ err i m t := by
    intro i m t
    exact norm_nonneg _
  have hres_tendsto : ∀ δ, 0 < δ → ∃ m, ∀ i (t : BrownianCubeAnchor d),
      err i m t ≤ δ := by
    intro δ hδ
    exact AlignmentUniformGeometricApproximation.uniform_small_of_squared_geometric
      err C q (fun i => (hqpos i).le) hqone herr0
      (fun i m t => hres t i m) hδ
  let Cenergy : ℝ := (∏ i : Fin d, (1+C (ep i)/q (ep i))) *
      ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  let Cbudget : ℝ := AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
      AlignmentGeometricRanks.polynomialBudget (Real.rpow 2 (-2*h)) (ν-1)
  let Cvar : ℝ := Cenergy * Cbudget
  let Cdim : ℝ := (2:ℝ) * (∏ i : Fin d, (A i : ℝ)) *
      ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  have hgap : ∀ j, 0 < 1-Real.rpow 2 (-(w j-1)) := by
    intro j
    have hneg : -(w j-1) < 0 := by linarith [hw j]
    have hpow := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2) hneg
    exact sub_pos.mpr hpow
  have hCenergy : 0 ≤ Cenergy := by
    dsimp [Cenergy]
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      have hq := hqpos (ep i)
      have hci := hC (ep i)
      have hfactor : 0 ≤ 1 + C (ep i) / q (ep i) := by positivity
      exact hfactor
    · apply Finset.prod_nonneg
      intro j hj
      have hg := hgap j
      exact inv_nonneg.mpr (le_of_lt hg)
  have hCbudget : 0 ≤ Cbudget := by
    dsimp [Cbudget]
    exact add_nonneg
      (AlignmentGeometricRanks.polynomialBudget_nonneg (by norm_num) 0)
      (AlignmentGeometricRanks.polynomialBudget_nonneg hqpos0.le (ν-1))
  have hCvar : 0 ≤ Cvar := by
    dsimp [Cvar]
    exact mul_nonneg hCenergy hCbudget
  have hCdim : 0 ≤ Cdim := by
    dsimp [Cdim]
    apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      · apply Finset.prod_nonneg
        intro i hi
        exact_mod_cast Nat.zero_le (A i)
    · apply Finset.prod_nonneg
      intro j hj
      have hg := hgap j
      exact inv_nonneg.mpr (le_of_lt hg)
  let F : ℕ → Type := fun M => ∀ i : Fin d, GradedFrameIndex (U i) M
  let eframe : ∀ M, F M → FullProductL2 d := fun M a =>
    gradedTensorFrame U hfinite hnested M a
  let gr : ∀ M, F M → ℕ := fun M a =>
    weightedProfileGrade α r (profileNat (fun i => (a i).1))
  let hFfinite : ∀ M, Fintype (F M) := fun _ => Pi.instFintype
  let hFdec : ∀ M, DecidableEq (F M) := fun _ => Classical.decEq _
  have hFnonempty : ∀ M, Nonempty (F M) := by
    intro M
    refine ⟨fun i => ?_⟩
    exact ⟨⟨0, by omega⟩, Classical.choice (hbase i)⟩
  have horth : ∀ M, letI : Fintype (F M) := hFfinite M
      letI : DecidableEq (F M) := hFdec M
      ∀ a b, ⟪eframe M a, eframe M b⟫ = if a=b then 1 else 0 := by
    intro M
    letI := hFfinite M
    letI := hFdec M
    intro a b
    exact orthonormal_iff_ite.mp (gradedTensorFrame_orthonormal U hfinite hnested M) a b
  have henergy : ∀ M, ∀ g : ℕ, ∀ t : BrownianCubeAnchor d,
      letI : Fintype (F M) := hFfinite M
      (∑ a : {a : F M // gr M a = g},
        ⟪fractionalSheetFeature H hH t, eframe M a.1⟫^2) ≤
          Cenergy * (((g+1:ℕ):ℝ)^(ν-1)) * (Real.rpow 2 (-2*h))^g := by
    intro M g t
    letI := hFfinite M
    have hprof := fractionalSheet_weightedGrade_energy_profile_le_of_minimumMultiplicity
      (ν:=ν) (e:=e) (M:=M) (by omega) U hfinite hnested H α hH
      (by intro i; dsimp [α]) r hr hmα
      (fun _ => (1:ℝ)) C q
      (fun _ => by norm_num) hC hqpos
      (by intro i; dsimp [q,α]; congr 1 <;> ring)
      (fun t i => by
        have hn := normalizedAxis_norm_le_one (H i) (hH i).1 (hH i).2
          (cubeCoordinate i t)
        have hn0 := norm_nonneg (normalizedAxis (H i) (hH i).1 (hH i).2
          (cubeCoordinate i t))
        nlinarith)
      hres g t
    have hbase : Real.rpow 2 (-(2*r-1)) = Real.rpow 2 (-2*h) := by
      congr 1
      dsimp [r]
      ring
    have hformula :
        (∑ a : {a : F M // gr M a = g},
          ⟪fractionalSheetFeature H hH t, eframe M a.1⟫^2) =
        (∑ a : {a : (i : Fin d) → GradedFrameIndex (U i) M //
            weightedProfileGrade α r (profileNat (fun i => (a i).1)) = g},
          ⟪fractionalSheetFeature H hH t,
            gradedTensorFrame U hfinite hnested M a.1⟫^2) := by
      exact Fintype.sum_equiv (Equiv.refl _) _ _ (by intro a; rfl)
    have hpowbase : (Real.rpow 2 (-(2*r-1)))^g =
        (Real.rpow 2 (-2*h))^g := congrArg (fun x : ℝ => x^g) hbase
    rw [hpowbase] at hprof
    calc
      _ = (∑ a : {a : (i : Fin d) → GradedFrameIndex (U i) M //
          weightedProfileGrade α r (profileNat (fun i => (a i).1)) = g},
          ⟪fractionalSheetFeature H hH t,
            gradedTensorFrame U hfinite hnested M a.1⟫^2) := hformula
      _ ≤ Cenergy * (Real.rpow 2 (-2*h))^g * (((g+1:ℕ):ℝ)^(ν-1)) := by
        change _ ≤ Cenergy * (Real.rpow 2 (-2*h))^g * (((g+1:ℕ):ℝ)^(ν-1)) at hprof
        exact hprof
      _ = Cenergy * (((g+1:ℕ):ℝ)^(ν-1)) * (Real.rpow 2 (-2*h))^g := by ring
  have hfiber : ∀ M N, letI : Fintype (F M) := hFfinite M
      ∀ g : Fin (N+1),
        (Fintype.card {a : F M // gr M a = g.val} : ℝ) ≤
          Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^(ν-1)) := by
    intro M N
    letI := hFfinite M
    intro g
    have hr0 : 0 < r := by linarith
    have hcount := fractionalSheet_weightedFiber_card_le_minimumMultiplicity
      (M:=M) (n:=g.val) hr0 (by omega) U α A hcard hmα
    have hpow : Real.rpow 2 ((g.val:ℝ)+1) = 2 * (2:ℝ)^g.val := by
      have hcast : (g.val:ℝ)+1 = ((g.val+1:ℕ):ℝ) := by norm_num
      calc
        Real.rpow 2 ((g.val:ℝ)+1) =
            Real.rpow 2 ((g.val+1:ℕ):ℝ) := by rw [hcast]
        _ = (2:ℝ)^(g.val+1) := Real.rpow_natCast _ _
        _ = 2 * (2:ℝ)^g.val := by rw [pow_succ]; ring
    rw [hpow] at hcount
    change (Fintype.card {a : F M // gr M a = g.val} : ℝ) ≤
      (∏ i : Fin d, (A i : ℝ)) *
        ((2:ℝ)*(2:ℝ)^g.val *
          ((((g.val+1:ℕ):ℝ)^(ν-1)) *
            ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))
      at hcount
    calc
      _ ≤ (∏ i : Fin d, (A i : ℝ)) *
          ((2:ℝ)*(2:ℝ)^g.val *
            ((((g.val+1:ℕ):ℝ)^(ν-1)) *
              ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := hcount
      _ = Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^(ν-1)) := by
        dsimp [Cdim]
        ring
  have hhHolder : ∀ z w, ‖fractionalSheetFeature H hH z-
      fractionalSheetFeature H hH w‖^2 ≤ (d:ℝ)^2*(dist z w)^(2*h) := by
    intro z w
    exact fractionalSheetFeature_squared_holder H hH h hh
      (fun i => hmin.1 i) z w
  have hincrement : ∀ M N, letI : Fintype (F M) := hFfinite M
      ∀ z w, ∑ a : F M,
        (contractionScale η N (gr M a) *
          (⟪fractionalSheetFeature H hH z, eframe M a⟫-
            ⟪fractionalSheetFeature H hH w, eframe M a⟫))^2 ≤
        (d:ℝ)^2*(dist z w)^(2*h) := by
    intro M N
    letI := hFfinite M
    intro z w
    have hhelper := contracted_frame_increment_le_of_holder
      (d:=d) (H:=FullProductL2 d) (fractionalSheetFeature H hH)
      (eframe M) (gradedTensorFrame_orthonormal U hfinite hnested M)
      (gr M) η hη.le hη1 N h ((d:ℝ)^2) hh (sq_nonneg (d:ℝ)) hhHolder
    simpa [eframe, gr] using hhelper z w
  have happrox : ∀ ε, 0 < ε → ∃ M,
      letI : Fintype (F M) := hFfinite M
      letI : DecidableEq (F M) := hFdec M
      ∀ t, ‖fractionalSheetFeature H hH t -
        projection (eframe M) (fractionalSheetFeature H hH t)‖ ≤ ε := by
    intro ε hε
    let δ : ℝ := ε / ((d:ℝ)^2)
    have hdpos : 0 < (d:ℝ) := by exact_mod_cast (show 0 < ν+e by omega)
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨M,hscalar⟩ := hres_tendsto δ hδ
    refine ⟨M,?_⟩
    letI := hFfinite M
    letI := hFdec M
    intro t
    have hproj := fractionalSheetFeature_finiteFrameProjection_error_le
      (d:=d) (by omega) U hfinite hnested H hH (fun _ => δ)
      (fun _ => le_of_lt hδ) (by intro i t; exact hscalar i t) t
    have hprojEq : projection (eframe M) (fractionalSheetFeature H hH t) =
        projection (gradedTensorFrame U hfinite hnested M)
          (fractionalSheetFeature H hH t) :=
      AlignmentFintypeIrrelevance.projection_fintype_eq
        (hFfinite M) Pi.instFintype (gradedTensorFrame U hfinite hnested M)
        (fractionalSheetFeature H hH t)
    have hprojLocal : ‖fractionalSheetFeature H hH t -
        projection (eframe M) (fractionalSheetFeature H hH t)‖ ≤
        (d:ℝ) * ∑ i : Fin d, δ := by
      rw [hprojEq]
      exact hproj
    have hsum : (∑ i : Fin d, δ) = (d:ℝ)*δ := by simp
    rw [hsum] at hprojLocal
    have hdge1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (show 1 ≤ ν+e by omega)
    have hproj' : ‖fractionalSheetFeature H hH t -
        projection (eframe M) (fractionalSheetFeature H hH t)‖ ≤ (d:ℝ)^2*δ := by
      simpa [pow_two, mul_assoc] using hprojLocal
    calc
      ‖fractionalSheetFeature H hH t - projection (eframe M) (fractionalSheetFeature H hH t)‖
          ≤ (d:ℝ)^2*δ := hproj'
      _ ≤ ε := by
        dsimp [δ]
        field_simp [hdne]
        nlinarith [hε, hdge1]
  exact fractionalSheet_upperLog_of_uniform_frame_profiles
    (d:=d) (by omega) H hH h ν hν hmin Cvar ((d:ℝ)^2) Cdim η
    hCvar (sq_nonneg _) hCdim hη hη1 F hFfinite hFdec hFnonempty
    eframe gr horth
    (by
      intro M N
      letI := hFfinite M
      intro z
      have hhprof : ∀ g : ℕ,
          (∑ a : {a : F M // gr M a = g},
            (⟪fractionalSheetFeature H hH z, eframe M a.1⟫)^2) ≤
            Cenergy * (((g+1:ℕ):ℝ)^(ν-1)) * (Real.rpow 2 (-2*h))^g :=
        by intro g; exact henergy M g z
      have hcv := graded_contracted_square_sum_le_uniform (gr M)
        (fun a => ⟪fractionalSheetFeature H hH z, eframe M a⟫)
        hqpos0 hqone0 hηsq hCenergy (ν-1) N hhprof
      have hpow : (Real.rpow 2 (-2*h))^N =
          (Real.rpow 2 (-2*h*(N:ℝ)/2))^2 := by
        simpa only [show -2*h = -(2*h) by ring,
          show -2*h*(N:ℝ)/2 = -(2*h)*(N:ℝ)/2 by ring] using
            (audit_rpow_dyadic_rate_sq (2*h) N).symm
      calc
        _ ≤ Cenergy * (Real.rpow 2 (-2*h))^N *
            (((N+1:ℕ):ℝ)^(ν-1)) * Cbudget := by
          simpa [Cbudget, mul_assoc, mul_left_comm, mul_comm] using hcv
        _ = Cvar * (Real.rpow 2 (-(2*h)*(N:ℝ)/2))^2 *
            (((N+1:ℕ):ℝ)^(ν-1)) := by
          rw [hpow]
          dsimp [Cvar, Cbudget]
          ring)
    hincrement hfiber happrox

end BrownianSharp.AlignmentAuditGaussianScalarClosure
