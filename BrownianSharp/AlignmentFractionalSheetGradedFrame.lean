import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentNestedProjectionEnergy
import BrownianSharp.AlignmentNestedProjectionDecay
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy
import BrownianSharp.AlignmentFractionalPadding
import BrownianSharp.AlignmentFractionalPaddingPermutation
import BrownianSharp.AlignmentFractionalGenericGradeCounts
import BrownianSharp.GaussianProjection
import Mathlib.Tactic

/-! Generic finite graded coordinate frames tensorize in the actual
whole-line product L² space. The source filtration remains abstract, so this
module composes with polynomial, past-tail, or mixed filtrations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open HaarQuarter

namespace BrownianSharp.AlignmentFractionalSheetGradedFrame

open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionEnergy
open BrownianSharp.AlignmentNestedProjectionDecay
open BrownianSharp.AlignmentSigmaFiniteL2Tensor
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy
open BrownianSharp.AlignmentFractionalPadding
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalGenericGradeCounts
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.GaussianProjection
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.Latest

abbrev AxisL2 := FullLineL2
abbrev TensorL2 (d : ℕ) := FullProductL2 d

/-- Tensor product of the coordinate graded frames for abstract nested
finite-dimensional source filtrations. -/
def gradedTensorFrame {d : ℕ} (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ)
    (a : ∀ i : Fin d, GradedFrameIndex (U i) N) : TensorL2 d :=
  productVector (fun i => gradedFrame (U i) (hfinite i) N (a i))

instance gradedTensorFrame_span_finiteDimensional {d : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ) :
    FiniteDimensional ℝ ↥(Submodule.span ℝ
      (Set.range (gradedTensorFrame U hfinite hnested N))) :=
  FiniteDimensional.span_of_finite ℝ
    (Set.finite_range (gradedTensorFrame U hfinite hnested N))

theorem gradedTensorFrame_orthonormal {d : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ) :
    Orthonormal ℝ (gradedTensorFrame U hfinite hnested N) := by
  classical
  apply productVector_orthonormal
  intro i
  exact gradedFrame_orthonormal (U i) (hfinite i) (hnested i) N

theorem gradedTensorFrame_inner {d : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ)
    (a b : ∀ i : Fin d, GradedFrameIndex (U i) N) :
    ⟪gradedTensorFrame U hfinite hnested N a,
      gradedTensorFrame U hfinite hnested N b⟫ =
        ∏ i, ⟪gradedFrame (U i) (hfinite i) N (a i),
          gradedFrame (U i) (hfinite i) N (b i)⟫ := by
  exact productVector_inner _ _

/-- The span of the tensor graded frame is the tensor product of the
coordinate truncations, expressed as the exact projection expansion needed
for feature approximation. -/
theorem gradedTensorFrame_span_starProjection_eq_sum {d : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ) (x : TensorL2 d) :
    (Submodule.span ℝ (Set.range (gradedTensorFrame U hfinite hnested N))).starProjection x =
      ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) N),
        ⟪x, gradedTensorFrame U hfinite hnested N a⟫ •
          gradedTensorFrame U hfinite hnested N a := by
  classical
  let f := gradedTensorFrame U hfinite hnested N
  let W : Submodule ℝ (TensorL2 d) := Submodule.span ℝ (Set.range f)
  have horth : Orthonormal ℝ f := gradedTensorFrame_orthonormal U hfinite hnested N
  let q := BrownianSharp.finiteOrthonormalProjection f x
  have hmem : q ∈ W := by
    dsimp [q, BrownianSharp.finiteOrthonormalProjection, W]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hres : x-q ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    dsimp [W] at hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro z ⟨a,rfl⟩
      exact BrownianSharp.finiteProjection_residual_orthogonal f x
        (orthonormal_iff_ite.mp horth) a
    · simp
    · intro y z hy hz hpy hpz
      rw [inner_add_right, hpy, hpz]
      simp
    · intro c y hy hpy
      rw [inner_smul_right, hpy]
      simp
  have hp := W.eq_starProjection_of_mem_orthogonal hmem hres
  simpa [W, q, f, BrownianSharp.finiteOrthonormalProjection] using hp

/-- The orthogonal projection onto the graded tensor frame is exactly the
finite Gaussian-coordinate projection used by the reverse theorem. -/
theorem gradedTensorFrame_starProjection_eq_gaussianProjection {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (x : TensorL2 d) :
    (Submodule.span ℝ (Set.range (gradedTensorFrame U hfinite hnested M))).starProjection x =
      GaussianProjection.projection (gradedTensorFrame U hfinite hnested M) x := by
  rw [gradedTensorFrame_span_starProjection_eq_sum]
  unfold GaussianProjection.projection
  apply Finset.sum_congr rfl
  intro a ha
  rw [real_inner_comm]

/-- Actual normalized Mandelbrot–van Ness sheet features have exact
coordinatewise coefficient factorization against every elementary tensor
source vector in the whole-line product L² space. -/
theorem fractionalSheetFeature_inner_product {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (t : BrownianCubeAnchor d)
    (v : Fin d → FullLineL2) :
    ⟪fractionalSheetFeature H hH t, productVector v⟫ =
      ∏ i, ⟪normalizedAxis (H i) (hH i).1 (hH i).2
        (cubeCoordinate i t), v i⟫ := by
  change ⟪productVector
      (fun i => normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)),
    productVector v⟫ = _
  exact productVector_inner _ _

/-- Specialization of the coefficient factorization to the abstract graded
frame. -/
theorem fractionalSheetFeature_inner_gradedTensorFrame {d : ℕ}
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1)) (N : ℕ)
    (t : BrownianCubeAnchor d)
    (a : ∀ i : Fin d, GradedFrameIndex (U i) N) :
    ⟪fractionalSheetFeature H hH t,
      gradedTensorFrame U hfinite hnested N a⟫ =
        ∏ i, ⟪normalizedAxis (H i) (hH i).1 (hH i).2
          (cubeCoordinate i t), gradedFrame (U i) (hfinite i) N (a i)⟫ := by
  exact fractionalSheetFeature_inner_product H hH t
    (fun i => gradedFrame (U i) (hfinite i) N (a i))

private theorem sum_pi_prod_sq {d : ℕ} (J : Fin d → Type*) [∀ i, Fintype (J i)]
    (c : ∀ i, J i → ℝ) :
    (∑ x : (∀ i, J i), (∏ i, c i (x i)) ^ 2) =
      ∏ i : Fin d, ∑ j : J i, c i j ^ 2 := by
  classical
  have hpow (x : (∀ i, J i)) :
      (∏ i : Fin d, c i (x i)) ^ 2 = ∏ i : Fin d, c i (x i) ^ 2 := by
    simpa using (Finset.prod_pow (Finset.univ : Finset (Fin d)) 2
      (fun i => c i (x i))).symm
  simp_rw [hpow]
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (J i))) (fun i j => c i j ^ 2)).symm

/-- Exact product-grade coefficient energy for actual normalized MvN sheet
features. It uses only the coordinate father norm and scalar projection
residuals; the filtration itself is arbitrary. -/
theorem fractionalSheetFeature_gradeFiber_energy_le_of_projection_residual
    {d M : ℕ} (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (t : BrownianCubeAnchor d)
    (C₀ C q : Fin d → ℝ)
    (hC₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i, 0 < q i)
    (hfather : ∀ i,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)‖ ^ 2 ≤ C₀ i)
    (hres : ∀ i m,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i m).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ^ 2 ≤
        C i * q i ^ m)
    (s : Fin d → Fin (M+1)) :
    (∑ a : (∀ i, GradeIndex (U i) (s i).val),
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M (fun i => (⟨s i,a i⟩ :
          GradedFrameIndex (U i) M))⟫ ^ 2) ≤
      ∏ i : Fin d, (C₀ i + C i / q i) * q i ^ (s i).val := by
  classical
  let J : Fin d → Type := fun i => GradeIndex (U i) (s i).val
  let embed : ∀ i, J i → GradedFrameIndex (U i) M := fun i j => ⟨s i,j⟩
  let c : ∀ i, J i → ℝ := fun i j =>
    ⟪normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t),
      gradedFrame (U i) (hfinite i) M (embed i j)⟫
  have hfactor :
      (∑ a : (∀ i, J i),
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M (fun i => embed i (a i))⟫ ^ 2) =
        ∏ i : Fin d, ∑ j : J i, c i j ^ 2 := by
    calc
      _ = ∑ a : (∀ i, J i), (∏ i, c i (a i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [fractionalSheetFeature_inner_gradedTensorFrame]
      _ = _ := sum_pi_prod_sq J c
  have haxis (i : Fin d) (g : ℕ) :
      (∑ j : GradeIndex (U i) g,
        ⟪normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t),
          gradeFamily (U i) (hfinite i) g j⟫ ^ 2) ≤
        (C₀ i + C i / q i) * q i ^ g := by
    have hscalar := gradeFamily_energy_le_geometric (U i) (hfinite i)
      (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))
      (C₀ i) (C i) (q i) (hC₀ i) (hC i) (hq i)
      (hfather i) (hres i)
    simpa using hscalar g
  rw [hfactor]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun j hj => sq_nonneg (c i j)
  · intro i hi
    have heq :
        (∑ j : J i, c i j ^ 2) =
          ∑ j : GradeIndex (U i) (s i).val,
            ⟪normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t),
              gradeFamily (U i) (hfinite i) (s i).val j⟫ ^ 2 := by
      rfl
    rw [heq]
    exact haxis i (s i).val

private abbrev SheetGradeFiber {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (s : HaarGradeProfileBox d M) :=
  ProductGradeFiber U s

/-! The next theorem is the weighted-slab version of the preceding exact
profile energy.  It is deliberately stated for arbitrary coordinate
filtrations: the concrete polynomial/past-tail construction supplies only
the coordinate projection residual estimates. -/

theorem fractionalSheetFeature_weightedGrade_energy_le_of_projection_residual
    {ν e M : ℕ} (hν : 0 < ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H : Fin (ν+e) → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (r : ℝ) (hr : 1/2 < r) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j)
    (α : Fin (ν+e) → ℝ)
    (horder : α = paddedOrders r (fun j => r * w j))
    (hHα : ∀ i, H i + 1/2 = α i)
    (t : BrownianCubeAnchor (ν+e))
    (C₀ C q : Fin (ν+e) → ℝ)
    (hC₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i, 0 < q i)
    (hqeq : ∀ i, q i = Real.rpow 2 (-(2*α i-1)))
    (hfather : ∀ i,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)‖ ^ 2 ≤ C₀ i)
    (hres : ∀ i m,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i m).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ^ 2 ≤
        C i * q i ^ m)
    (n : ℕ) :
    (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
      (∏ i : Fin (ν+e), (C₀ i + C i / q i)) *
        (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
  classical
  let D : Fin (ν+e) → ℝ := fun i => C₀ i + C i / q i
  subst α
  let α0 : Fin (ν+e) → ℝ := paddedOrders r (fun j => r * w j)
  let profileFiber : Type := {s : HaarGradeProfileBox (ν+e) M //
      weightedProfileGrade α0 r (profileNat s) = n}
  let profEquiv := productGradeFiberEquiv (M := M) (n := n) U α0 r
  let splitEquiv := weightedProfileSplitEquiv (ν := ν) (e := e) (M := M)
      (n := n) (r := r) (ne_of_gt (lt_trans (by norm_num) hr)) w
  have hprofile (s : HaarGradeProfileBox (ν+e) M) :
      (∑ a : SheetGradeFiber U s,
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M
            (fun i => (⟨s i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2) ≤
      ∏ i : Fin (ν+e), D i * q i ^ (s i).val := by
    exact fractionalSheetFeature_gradeFiber_energy_le_of_projection_residual
      U hfinite hnested H hH t C₀ C q hC₀ hC hq hfather hres s
  have hsum_reindex :
      (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
          weightedProfileGrade α0 r (profileNat (fun i => (a i).1)) = n},
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) =
      ∑ s : profileFiber, ∑ a : SheetGradeFiber U s.1,
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M
            (fun i => (⟨s.1 i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 := by
    calc
      _ = ∑ x : (Σ s : profileFiber, SheetGradeFiber U s.1),
          ⟪fractionalSheetFeature H hH t,
            gradedTensorFrame U hfinite hnested M
              (fun i => (⟨x.1.1 i, x.2 i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 :=
            Fintype.sum_equiv profEquiv _ _ (by intro a; rfl)
      _ = ∑ s : profileFiber, ∑ a : SheetGradeFiber U s.1,
          ⟪fractionalSheetFeature H hH t,
            gradedTensorFrame U hfinite hnested M
              (fun i => (⟨s.1 i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 := by
            rw [Fintype.sum_sigma]
  let Dprod : ℝ := ∏ i : Fin (ν+e), D i
  have hweighted_sum :
      (∑ s : profileFiber, ∏ i : Fin (ν+e), D i * q i ^ (s.1 i).val) =
      Dprod * ∑ p : {p : ActiveBox ν M × InactiveBox e M //
          weightedGradeFloor w p.1 p.2 = n},
        (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
          ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := by
    calc
      _ = ∑ s : profileFiber, Dprod *
          ∏ i : Fin (ν+e), q i ^ (s.1 i).val := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [show (∏ i : Fin (ν+e), D i * q i ^ (s.1 i).val) =
              Dprod * ∏ i : Fin (ν+e), q i ^ (s.1 i).val by
                simp [Dprod, Finset.prod_mul_distrib]]
      _ = Dprod * ∑ s : profileFiber,
          ∏ i : Fin (ν+e), q i ^ (s.1 i).val := by rw [Finset.mul_sum]
      _ = Dprod * ∑ p : {p : ActiveBox ν M × InactiveBox e M //
            weightedGradeFloor w p.1 p.2 = n},
          (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
            ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := by
          congr 1
          exact Fintype.sum_equiv splitEquiv _ _ (by
            intro s
            have hp : splitHaarProfileEquiv s.1 = (splitEquiv s).1 := rfl
            have hactive (i : Fin ν) :
                (s.1 (Fin.castAdd e i)).val = ((splitEquiv s).1.1 i).val :=
              congrArg Fin.val (congrFun (congrArg Prod.fst hp) i)
            have hinactive (j : Fin e) :
                (s.1 (Fin.natAdd ν j)).val = ((splitEquiv s).1.2 j).val :=
              congrArg Fin.val (congrFun (congrArg Prod.snd hp) j)
            calc
              _ = ∏ x : Fin ν ⊕ Fin e,
                  q (finSumFinEquiv x) ^ (s.1 (finSumFinEquiv x)).val := by
                    symm
                    exact Fintype.prod_equiv finSumFinEquiv _ _ (by intro x; rfl)
              _ = (∏ i : Fin ν,
                    Real.rpow 2 (-(2*r-1))^((splitEquiv s).1.1 i).val) *
                  ∏ j : Fin e,
                    Real.rpow 2 (-(2*r*w j-1))^((splitEquiv s).1.2 j).val := by
                    rw [Fintype.prod_sum_type]
                    congr 1
                    · apply Finset.prod_congr rfl
                      intro i hi
                      change q (Fin.castAdd e i) ^ (s.1 (Fin.castAdd e i)).val = _
                      rw [hqeq, hactive i]
                      simp [paddedOrders, finSumFinEquiv_symm_apply_castAdd]
                    · apply Finset.prod_congr rfl
                      intro j hj
                      change q (Fin.natAdd ν j) ^ (s.1 (Fin.natAdd ν j)).val = _
                      rw [hqeq, hinactive j]
                      simp [paddedOrders, finSumFinEquiv_symm_apply_natAdd]
                      congr 1
                      congr 1
                      ring)
  rw [hsum_reindex]
  calc
    _ ≤ ∑ s : profileFiber, ∏ i : Fin (ν+e), D i * q i ^ (s.1 i).val := by
      apply Finset.sum_le_sum
      intro s hs
      exact hprofile s.1
    _ = Dprod *
        ∑ p : {p : ActiveBox ν M × InactiveBox e M //
          weightedGradeFloor w p.1 p.2 = n},
          (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
            ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := hweighted_sum
    _ ≤ Dprod * (Real.rpow 2 (-(2*r-1)*n) *
          ((((n+1:ℕ):ℝ)^(ν-1) *
            ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
      have hD : 0 ≤ Dprod := Finset.prod_nonneg fun i hi =>
        add_nonneg (hC₀ i) (div_nonneg (hC i) (hq i).le)
      have hbox := weighted_box_profile_subtype_energy_le
        (M := M) (n := n) (C := Dprod) hν hr hD w hw
      calc
        _ = ∑ p : {p : ActiveBox ν M × InactiveBox e M //
            weightedGradeFloor w p.1 p.2 = n},
              Dprod * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
                ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val) := by
              rw [Finset.mul_sum]
        _ ≤ _ := hbox

private theorem rpow_two_nat_power (β : ℝ) (k : ℕ) :
    (Real.rpow 2 (-β))^k = Real.rpow 2 (-β * (k:ℝ)) := by
  calc
    (Real.rpow 2 (-β))^k = (Real.rpow 2 (-β))^(k:ℝ) := by
      rw [← Real.rpow_natCast]
    _ = Real.rpow 2 (-β * (k:ℝ)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-β) (k:ℝ)).symm

/-- Uniform actual-sheet coefficient energy in each weighted grade, in the
`C ρ^g (g+1)^k` form consumed by the Gaussian reverse core. -/
theorem fractionalSheet_weightedGrade_energy_profile_le
    {ν e M : ℕ} (hν : 0 < ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H : Fin (ν+e) → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (r : ℝ) (hr : 1/2 < r) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j)
    (α : Fin (ν+e) → ℝ)
    (horder : α = paddedOrders r (fun j => r * w j))
    (hHα : ∀ i, H i + 1/2 = α i)
    (C₀ C q : Fin (ν+e) → ℝ)
    (hC₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i, 0 < q i)
    (hqeq : ∀ i, q i = Real.rpow 2 (-(2*α i-1)))
    (hfather : ∀ t : BrownianCubeAnchor (ν+e), ∀ i,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)‖ ^ 2 ≤ C₀ i)
    (hres : ∀ t : BrownianCubeAnchor (ν+e), ∀ i m,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i m).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ^ 2 ≤
        C i * q i ^ m) :
    let Cvar : ℝ :=
      (∏ i : Fin (ν+e), (C₀ i + C i / q i)) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
    ∀ n : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
      (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
          weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
        Cvar * (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1)) := by
  classical
  let D : Fin (ν+e) → ℝ := fun i => C₀ i + C i / q i
  let Cvar : ℝ :=
      (∏ i : Fin (ν+e), D i) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  change ∀ n : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
    (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
      Cvar * (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1))
  intro n t
  have hslab := fractionalSheetFeature_weightedGrade_energy_le_of_projection_residual
    (M := M)
    hν U hfinite hnested H hH r hr w hw α horder hHα t C₀ C q hC₀ hC hq hqeq
    (hfather t) (hres t) n
  have hpow := rpow_two_nat_power (2*r-1) n
  change (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
    ⟪fractionalSheetFeature H hH t,
      gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
    Cvar * (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1))
  dsimp [Cvar, D]
  calc
    _ ≤ (∏ i : Fin (ν+e), (C₀ i + C i / q i)) *
        (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := hslab
    _ = (∏ i : Fin (ν+e), (C₀ i + C i / q i)) *
        (∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹) *
          (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1)) := by
          rw [← hpow]
          ring

/-- Arbitrary-order form of the actual sheet variance profile. The minimum
coordinates are moved to the first block internally, so callers provide the
original order vector and minimum-multiplicity hypothesis rather than a
pre-permuted/padded parameterization. The frame and process coordinates remain
in their original order. -/
theorem fractionalSheet_weightedGrade_energy_profile_le_of_minimumMultiplicity
    {ν e M : ℕ} (hν : 0 < ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H α : Fin (ν+e) → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (hHα : ∀ i, H i + 1/2 = α i)
    (r : ℝ) (hr : 1/2 < r)
    (hm : Latest.minimumMultiplicity α r ν)
    (C₀ C q : Fin (ν+e) → ℝ)
    (hC₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i, 0 < q i)
    (hqeq : ∀ i, q i = Real.rpow 2 (-(2*α i-1)))
    (hfather : ∀ t : BrownianCubeAnchor (ν+e), ∀ i,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)‖ ^ 2 ≤ C₀ i)
    (hres : ∀ t : BrownianCubeAnchor (ν+e), ∀ i m,
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i m).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ^ 2 ≤
        C i * q i ^ m) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    let Cvar : ℝ :=
      (∏ i : Fin (ν+e), (C₀ (ep i) + C (ep i) / q (ep i))) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
    ∀ n : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
      (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
          weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
        Cvar * (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1)) := by
  classical
  unfold Latest.minimumMultiplicity at hm
  have hcard : (minimumIndexSet α r).card = ν := by
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation α r hcard
  let α' : Fin (ν+e) → ℝ := reindexOrders ep α
  let w : Fin e → ℝ := fun j => α' (Fin.natAdd ν j) / r
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w, α']
    have hr0 : 0 < r := by linarith
    rw [one_lt_div₀ hr0]
    exact minimumCoordinatePermutation_inactive_lt α r hcard hm.1 j
  have hr0 : 0 < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hpad₀ := reindexOrders_eq_paddedOrders α r hcard
  have hpad : α' = paddedOrders r (fun j => r * w j) := by
    have hpad' : reindexOrders ep α =
        paddedOrders r (fun j => r * (α' (Fin.natAdd ν j) / r)) := by
      rw [hpad₀]
      congr 1
      funext j
      change reindexOrders ep α (Fin.natAdd ν j) =
        r * (α' (Fin.natAdd ν j) / r)
      dsimp [α']
      field_simp [hrne]
    rw [show α' = reindexOrders ep α by rfl]
    convert hpad' using 1
  let Up : Fin (ν+e) → ℕ → Submodule ℝ AxisL2 := fun i n => U (ep i) n
  have hfinitep : ∀ i n, FiniteDimensional ℝ ↥(Up i n) := by
    intro i n
    exact hfinite (ep i) n
  have hnestedp : ∀ i n, Up i n ≤ Up i (n+1) := by
    intro i n
    exact hnested (ep i) n
  let Hp : Fin (ν+e) → ℝ := fun i => H (ep i)
  have hHp : ∀ i, 0 < Hp i ∧ Hp i < 1 := fun i => hH (ep i)
  have hHpα : ∀ i, Hp i + 1/2 = α' i := by
    intro i
    exact hHα (ep i)
  let qp : Fin (ν+e) → ℝ := fun i => q (ep i)
  let C₀p : Fin (ν+e) → ℝ := fun i => C₀ (ep i)
  let Cp : Fin (ν+e) → ℝ := fun i => C (ep i)
  have hC₀p : ∀ i, 0 ≤ C₀p i := fun i => hC₀ (ep i)
  have hCp : ∀ i, 0 ≤ Cp i := fun i => hC (ep i)
  have hqp : ∀ i, 0 < qp i := fun i => hq (ep i)
  have hqeqp : ∀ i, qp i = Real.rpow 2 (-(2*α' i-1)) := by
    intro i
    exact hqeq (ep i)
  let tp : BrownianCubeAnchor (ν+e) → BrownianCubeAnchor (ν+e) := fun t =>
    ⟨fun i => t.val (ep i), fun i => t.property (ep i)⟩
  let tpInv : BrownianCubeAnchor (ν+e) → BrownianCubeAnchor (ν+e) := fun t =>
    ⟨fun i => t.val (ep.symm i), fun i => t.property (ep.symm i)⟩
  have hfatherp : ∀ t, ∀ i,
      ‖normalizedAxis (Hp i) (hHp i).1 (hHp i).2 (cubeCoordinate i t)‖ ^ 2 ≤ C₀p i := by
    intro t i
    simpa [Hp, C₀p, tpInv, cubeCoordinate] using hfather (tpInv t) (ep i)
  have hresp : ∀ t i m,
      ‖normalizedAxis (Hp i) (hHp i).1 (hHp i).2 (cubeCoordinate i t) -
        (Up i m).starProjection
          (normalizedAxis (Hp i) (hHp i).1 (hHp i).2 (cubeCoordinate i t))‖ ^ 2 ≤
        Cp i * qp i ^ m := by
    intro t i m
    simpa [Hp, Up, Cp, qp, tpInv, cubeCoordinate] using hres (tpInv t) (ep i) m
  let Cvar : ℝ :=
      (∏ i : Fin (ν+e), (C₀p i + Cp i / qp i)) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  change ∀ n : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
    (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤
      Cvar * (Real.rpow 2 (-(2*r-1)))^n * (((n+1:ℕ):ℝ)^(ν-1))
  intro n t
  have hpadded := fractionalSheet_weightedGrade_energy_profile_le
    (M := M)
    hν Up hfinitep hnestedp Hp hHp r hr w hw α' hpad hHpα C₀p Cp qp
    hC₀p hCp hqp hqeqp hfatherp hresp n (tp t)
  let frameEquiv : (∀ i : Fin (ν+e), GradedFrameIndex (U i) M) ≃
      (∀ i : Fin (ν+e), GradedFrameIndex (Up i) M) :=
    (Equiv.piCongrLeft (fun i => GradedFrameIndex (U i) M) ep).symm
  have hgrade (a : ∀ i, GradedFrameIndex (U i) M) :
      weightedProfileGrade α' r (profileNat (fun i => (frameEquiv a i).1)) =
        weightedProfileGrade α r (profileNat (fun i => (a i).1)) := by
    unfold weightedProfileGrade profileNat
    apply congrArg Nat.floor
    simpa [α', reindexOrders, frameEquiv, Up] using Fintype.sum_equiv ep
      (fun i => (α (ep i) / r) * ((a (ep i)).1.val : ℝ))
      (fun j => (α j / r) * ((a j).1.val : ℝ))
      (by intro i; rfl)
  have hcoeff (a : ∀ i, GradedFrameIndex (U i) M) :
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M a⟫ =
      ⟪fractionalSheetFeature Hp hHp (tp t),
        gradedTensorFrame Up hfinitep hnestedp M (frameEquiv a)⟫ := by
    rw [fractionalSheetFeature_inner_gradedTensorFrame,
      fractionalSheetFeature_inner_gradedTensorFrame]
    dsimp [Hp, tp, cubeCoordinate, Up, frameEquiv]
    symm
    exact Fintype.prod_equiv ep
      (fun i => ⟪normalizedAxis (Hp i) (hHp i).1 (hHp i).2 (cubeCoordinate i (tp t)),
        gradedFrame (Up i) (hfinitep i) M (frameEquiv a i)⟫)
      (fun j => ⟪normalizedAxis (H j) (hH j).1 (hH j).2 (cubeCoordinate j t),
        gradedFrame (U j) (hfinite j) M (a j)⟫)
      (by intro i; rfl)
  let oldFiber := {a : ∀ i : Fin (ν+e), GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n}
  let newFiber := {a : ∀ i : Fin (ν+e), GradedFrameIndex (Up i) M //
      weightedProfileGrade α' r (profileNat (fun i => (a i).1)) = n}
  let fiberEquiv : oldFiber ≃ newFiber := {
    toFun := fun a => ⟨frameEquiv a.1, (hgrade a.1).trans a.2⟩
    invFun := fun a => ⟨frameEquiv.symm a.1,
      by
        have h := hgrade (frameEquiv.symm a.1)
        have h' : weightedProfileGrade α' r (profileNat (fun i => (a.1 i).1)) =
            weightedProfileGrade α r (profileNat (fun i => (frameEquiv.symm a.1 i).1)) := by
          simpa only [Equiv.apply_symm_apply] using h
        exact h'.symm.trans a.2⟩
    left_inv := by intro a; apply Subtype.ext; simp [frameEquiv]
    right_inv := by intro a; apply Subtype.ext; simp [frameEquiv]
  }
  have hsum :
      (∑ a : oldFiber,
        ⟪fractionalSheetFeature H hH t,
          gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) =
      ∑ a : newFiber,
        ⟪fractionalSheetFeature Hp hHp (tp t),
          gradedTensorFrame Up hfinitep hnestedp M a.1⟫ ^ 2 := by
    exact Fintype.sum_equiv fiberEquiv _ _ (by
      intro a
      rw [hcoeff]
      rfl)
  change (∑ a : oldFiber,
      ⟪fractionalSheetFeature H hH t,
        gradedTensorFrame U hfinite hnested M a.1⟫ ^ 2) ≤ _
  rw [hsum]
  simpa [Cvar, C₀p, Cp, qp] using hpadded

/-- The generic minimum-multiplicity estimate applied to whole-line sheet
frames.  This cumulative low-fiber count is the form needed by the diagonal
Gaussian contraction; its constant is independent of the truncation depth. -/
theorem fractionalSheet_weightedLowFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ AxisL2)
    (α : Fin (ν+e) → ℝ) (A : Fin (ν+e) → ℕ)
    (hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i * 2^g)
    (hm : Latest.minimumMultiplicity α r ν) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    (Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) ≤ n} : ℝ) ≤
      (∏ i : Fin (ν+e), (A i : ℝ)) *
        (Real.rpow 2 (n + 2) * (((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
  exact productGrade_weightedLowFiber_card_le_minimumMultiplicity
    hr hν U α A hA hm

/-- Exact weighted-grade count for the same whole-line frames. -/
theorem fractionalSheet_weightedFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (U : Fin (ν+e) → ℕ → Submodule ℝ AxisL2)
    (α : Fin (ν+e) → ℝ) (A : Fin (ν+e) → ℕ)
    (hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ A i * 2^g)
    (hm : Latest.minimumMultiplicity α r ν) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    (Fintype.card {a : ∀ i, GradedFrameIndex (U i) M //
      weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n} : ℝ) ≤
      (∏ i : Fin (ν+e), (A i : ℝ)) *
        (Real.rpow 2 (n + 1) * (((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
  exact productGrade_weightedFiber_card_le_minimumMultiplicity
    hr hν U α A hA hm

private theorem gradedFrame_projection_eq_sum {M : ℕ}
    (U : ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (x : AxisL2) :
    (U M).starProjection x =
      ∑ a : GradedFrameIndex U M,
        ⟪x, gradedFrame U hfinite M a⟫ • gradedFrame U hfinite M a := by
  let e := gradedFrame U hfinite M
  let W : Submodule ℝ AxisL2 := Submodule.span ℝ (Set.range e)
  let q := BrownianSharp.finiteOrthonormalProjection e x
  have hspan : W = U M := gradedFrame_span_eq U hfinite hnested M
  have horth : Orthonormal ℝ e := gradedFrame_orthonormal U hfinite hnested M
  have hmem : q ∈ U M := by
    rw [← hspan]
    dsimp [q, BrownianSharp.finiteOrthonormalProjection, W]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hres : x-q ∈ (U M)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    rw [← hspan] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro y ⟨a,rfl⟩
      exact BrownianSharp.finiteProjection_residual_orthogonal e x
        (orthonormal_iff_ite.mp horth) a
    · simp
    · intro y z hy hz hpy hpz
      rw [inner_add_right, hpy, hpz]
      simp
    · intro c y hy hpy
      rw [inner_smul_right, hpy]
      simp
  have hp := (U M).eq_starProjection_of_mem_orthogonal hmem hres
  simpa [q, e, BrownianSharp.finiteOrthonormalProjection] using hp

private theorem productProjectedTensor_mem_span {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (v : Fin d → AxisL2) :
    productVector (fun i => (U i M).starProjection (v i)) ∈
      Submodule.span ℝ (Set.range (gradedTensorFrame U hfinite hnested M)) := by
  classical
  let T := tensorContinuous (μ := fun _ : Fin d => (volume : Measure ℝ))
  let e : ∀ i : Fin d, GradedFrameIndex (U i) M → AxisL2 :=
    fun i => gradedFrame (U i) (hfinite i) M
  let c : ∀ i a, ℝ := fun i a => ⟪v i, e i a⟫
  have hcoord (i : Fin d) :
      (U i M).starProjection (v i) =
        ∑ a : GradedFrameIndex (U i) M, c i a • e i a :=
    gradedFrame_projection_eq_sum (U i) (hfinite i) (hnested i) (v i)
  have hexpand :
      productVector (fun i => (U i M).starProjection (v i)) =
        ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) M),
          (∏ i, c i (a i)) • gradedTensorFrame U hfinite hnested M a := by
    change T (fun i => (U i M).starProjection (v i)) = _
    calc
      _ = T (fun i => ∑ a : GradedFrameIndex (U i) M, c i a • e i a) := by
            congr 1
            funext i
            exact hcoord i
      _ = ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) M),
          T (fun i => c i (a i) • e i (a i)) := by
            exact T.map_sum (fun i a => c i a • e i a)
      _ = ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) M),
          (∏ i, c i (a i)) • gradedTensorFrame U hfinite hnested M a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [T.map_smul_univ]
            change (∏ i, c i (a i)) •
                tensorContinuous (fun i => gradedFrame (U i) (hfinite i) M (a i)) = _
            rw [tensorContinuous_apply]
            simp [gradedTensorFrame]
  rw [hexpand]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The actual whole-line sheet feature is uniformly close to the finite
graded tensor-frame projection whenever each scalar coordinate feature is
uniformly approximated by its source filtration. -/
theorem fractionalSheetFeature_gradedProjection_error_le
    {d M : ℕ} (hd : 0 < d)
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (δ : Fin d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hres : ∀ i (t : BrownianCubeAnchor d),
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i M).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ≤ δ i)
    (t : BrownianCubeAnchor d) :
    ‖fractionalSheetFeature H hH t -
      (Submodule.span ℝ (Set.range (gradedTensorFrame U hfinite hnested M))).starProjection
        (fractionalSheetFeature H hH t)‖ ≤ (d : ℝ) * ∑ i, δ i := by
  classical
  let T := tensorContinuous (μ := fun _ : Fin d => (volume : Measure ℝ))
  let v : Fin d → AxisL2 := fun i =>
    normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)
  let w : Fin d → AxisL2 := fun i => (U i M).starProjection (v i)
  let W : Submodule ℝ (TensorL2 d) :=
    Submodule.span ℝ (Set.range (gradedTensorFrame U hfinite hnested M))
  have hnormv (i : Fin d) : ‖v i‖ ≤ 1 := by
    exact normalizedAxis_norm_le_one (H i) (hH i).1 (hH i).2 (cubeCoordinate i t)
  have hproj (i : Fin d) : ‖(U i M).starProjection‖ ≤ 1 :=
    (U i M).starProjection_norm_le
  have hnormw (i : Fin d) : ‖w i‖ ≤ 1 := by
    calc
      ‖w i‖ ≤ ‖(U i M).starProjection‖ * ‖v i‖ :=
        (U i M).starProjection.le_opNorm (v i)
      _ ≤ 1 * 1 := by
        exact mul_le_mul (hproj i) (hnormv i) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hmaxv : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
    intro i
    exact hnormv i
  have hmaxw : ‖w‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
    intro i
    exact hnormw i
  have hdiff : ‖v-w‖ ≤ ∑ i : Fin d, δ i := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i hi => hδ i)).2
    intro i
    exact (hres i t).trans (Finset.single_le_sum
      (f := δ) (s := Finset.univ) (fun j hj => hδ j) (Finset.mem_univ i))
  have hTbound : ‖T‖ ≤ 1 := by
    dsimp [T, AlignmentSigmaFiniteL2Tensor.tensorContinuous]
    exact MultilinearMap.mkContinuous_norm_le _ (by norm_num)
      (fun _ => by simp [AlignmentSigmaFiniteL2Tensor.tensorMultilinear,
        AlignmentSigmaFiniteL2Tensor.productVector_norm])
  have hmult := T.norm_image_sub_le v w
  have hmult' : ‖T v - T w‖ ≤ (d:ℝ) * ∑ i : Fin d, δ i := by
    calc
      ‖T v - T w‖ ≤ ‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) * ‖v-w‖ := by
        simpa [Fintype.card_fin] using hmult
      _ ≤ 1 * (d:ℝ) * 1^(d-1) * (∑ i : Fin d, δ i) := by
        have hmax : max ‖v‖ ‖w‖ ≤ 1 := max_le hmaxv hmaxw
        have hsumδ : 0 ≤ ∑ i : Fin d, δ i := Finset.sum_nonneg fun i hi => hδ i
        have hdR : 0 ≤ (d:ℝ) := by positivity
        have hmaxpow : max ‖v‖ ‖w‖ ^ (d-1) ≤ 1 := by
          calc
            _ ≤ (1:ℝ)^(d-1) := pow_le_pow_left₀ (by positivity) hmax _
            _ = 1 := one_pow _
        have hTmul : ‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) ≤
            1 * (d:ℝ) * 1^(d-1) := by
          gcongr
        calc
          (‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1)) * ‖v-w‖ ≤
              (‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1)) * (∑ i : Fin d, δ i) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
          _ ≤ (1 * (d:ℝ) * 1^(d-1)) * (∑ i : Fin d, δ i) :=
            mul_le_mul_of_nonneg_right hTmul hsumδ
      _ = (d:ℝ) * ∑ i : Fin d, δ i := by simp
  have hactual : fractionalSheetFeature H hH t = T v := by
    simp [fractionalSheetFeature, T, v, tensorContinuous_apply, gradedTensorFrame]
  have hcandidate : productVector w ∈ W := by
    change productVector (fun i => (U i M).starProjection (v i)) ∈ W
    exact productProjectedTensor_mem_span U hfinite hnested v
  have hmin : ‖productVector v - W.starProjection (productVector v)‖ ≤
      ‖productVector v - productVector w‖ := by
    rw [Submodule.starProjection_minimal (U := W) (productVector v)]
    have hbdd : BddBelow (Set.range (fun y : W => ‖productVector v - (y : TensorL2 d)‖)) :=
      ⟨0, Set.forall_mem_range.mpr (fun y => norm_nonneg _)⟩
    exact ciInf_le hbdd ⟨productVector w, hcandidate⟩
  have hcandidate_eq : productVector w = T w := by
    simp [T, tensorContinuous_apply]
  have hfeature_eq : fractionalSheetFeature H hH t = productVector v := by
    simp [fractionalSheetFeature, v, tensorContinuous_apply]
  rw [hfeature_eq]
  calc
    ‖productVector v - W.starProjection (productVector v)‖ ≤
        ‖productVector v - productVector w‖ := by
      exact hmin
    _ = ‖T v - T w‖ := by rw [← hcandidate_eq]; simp [T, tensorContinuous_apply]
    _ ≤ (d:ℝ) * ∑ i : Fin d, δ i := hmult'

/-- Same projection residual in the exact `projection e` form consumed by
the Gaussian finite-grid lower bound. -/
theorem fractionalSheetFeature_finiteFrameProjection_error_le
    {d M : ℕ} (hd : 0 < d)
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (δ : Fin d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hres : ∀ i (t : BrownianCubeAnchor d),
      ‖normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t) -
        (U i M).starProjection
          (normalizedAxis (H i) (hH i).1 (hH i).2 (cubeCoordinate i t))‖ ≤ δ i)
    (t : BrownianCubeAnchor d) :
    ‖fractionalSheetFeature H hH t -
      GaussianProjection.projection (gradedTensorFrame U hfinite hnested M)
        (fractionalSheetFeature H hH t)‖ ≤ (d : ℝ) * ∑ i, δ i := by
  rw [← gradedTensorFrame_starProjection_eq_gaussianProjection]
  exact fractionalSheetFeature_gradedProjection_error_le hd U hfinite hnested
    H hH δ hδ hres t

end BrownianSharp.AlignmentFractionalSheetGradedFrame
