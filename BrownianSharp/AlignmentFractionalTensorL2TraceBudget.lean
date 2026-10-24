import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentFractionalL2TraceBudget
import BrownianSharp.AlignmentNestedProjectionTensor
import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature
import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentHilbertTraceRefinement
import BrownianSharp.AlignmentFractionalCubeL2ProjectionError

/-! Actual tensor-product Hilbert--Schmidt grade budgets for isotropic
Riemann--Liouville operators on the cube. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorL2TraceBudget

open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalL2OperatorSemigroup
open BrownianSharp.AlignmentFractionalL2TraceBudget
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.CameronMartin
open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalGradedPolynomialWidth
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentGaussianGradedTotalBudget
open BrownianSharp.AlignmentGeometricRanks
open HaarQuarter

abbrev AxisL2 := AlignmentFractionalL2.UnitL2

abbrev PolynomialTensorIndex (d q M : ℕ) :=
  ∀ i : Fin d, GradedFrameIndex (piecewisePolynomials q) M

def polynomialTensorGrade {d q M : ℕ} (a : PolynomialTensorIndex d q M) : ℕ :=
  ∑ i : Fin d, (a i).1.val

def polynomialTensorFrame {d q M : ℕ} :
    PolynomialTensorIndex d q M → UnitCubeL2 d :=
  tensorFrame (fun i => gradedFrame (piecewisePolynomials q)
    (fun n => piecewisePolynomials_finiteDimensional q n) M)

def fractionalTensorGradeCoefficient {d q M : ℕ} (β : ℝ)
    (hβ : 1/2 < β) (a : PolynomialTensorIndex d q M) : ℝ :=
  ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
    (polynomialTensorFrame a)‖^2

abbrev PolynomialTensorLowIndex (d q M N : ℕ) :=
  {a : PolynomialTensorIndex d q M // polynomialTensorGrade a ≤ N}

def polynomialTensorRectangleSpace {d q M : ℕ} :
    Submodule ℝ (UnitCubeL2 d) :=
  Submodule.span ℝ (Set.range (polynomialTensorFrame (d:=d) (q:=q) (M:=M)))

def polynomialTensorLowSpace {d q M N : ℕ} :
    Submodule ℝ (UnitCubeL2 d) :=
  Submodule.span ℝ (Set.range fun a : PolynomialTensorLowIndex d q M N =>
    polynomialTensorFrame a.1)

theorem polynomialTensorFrame_orthonormal {d q M : ℕ} :
    Orthonormal ℝ (polynomialTensorFrame (d:=d) (q:=q) (M:=M)) := by
  apply tensorFrame_orthonormal
  intro i
  exact gradedFrame_orthonormal (piecewisePolynomials q)
    (fun n => piecewisePolynomials_finiteDimensional q n)
    (piecewisePolynomials_le_succ q) M

theorem polynomialTensorRectangleSpace_finite {d q M : ℕ} :
    FiniteDimensional ℝ ↥(polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem polynomialTensorLowSpace_finite {d q M N : ℕ} :
    FiniteDimensional ℝ ↥(polynomialTensorLowSpace (d:=d) (q:=q) (M:=M) (N:=N)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem polynomialTensorLowSpace_le_rectangle {d q M N : ℕ} :
    polynomialTensorLowSpace (d:=d) (q:=q) (M:=M) (N:=N) ≤
      polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact Submodule.subset_span ⟨a.1,rfl⟩

theorem polynomialTensorLowIndex_card_le_layer_multiple
    {d q : ℕ} (hd : 2 ≤ d) (hq : 0 < q) :
    ∃ D : ℕ, 0 < D ∧ ∀ M N : ℕ,
      Fintype.card (PolynomialTensorLowIndex d q M N) ≤
        D * Fintype.card (LayerIndex d N) := by
  classical
  let α : Fin d → ℝ := fun _ => (1:ℝ)
  have hm : Latest.minimumMultiplicity α 1 d := by
    unfold Latest.minimumMultiplicity α
    constructor
    · intro i
      rfl
    · simp
  obtain ⟨D,hD,hcount⟩ := polynomial_tensor_weightedLowFiber_layer_multiple
    (ν:=d) (e:=0) (r:=1) hd (by norm_num : (0:ℝ)<1) α
    (fun _ => q) (fun _ => hq) hm
  refine ⟨D,hD,?_⟩
  intro M N
  have heq : PolynomialTensorLowIndex d q M N ≃
      {z : (∀ i : Fin d, GradedFrameIndex (fun m => piecewisePolynomials q m) M) //
        weightedProfileGrade α 1 (profileNat (fun i => (z i).1) : Fin d → ℕ) ≤ N} := by
    refine {
      toFun := fun z => ⟨z.1, ?_⟩
      invFun := fun z => ⟨z.1, ?_⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
    · have hgrade : weightedProfileGrade α 1
          (profileNat (fun i => (z.1 i).1) : Fin d → ℕ) =
          polynomialTensorGrade z.1 := by
        unfold weightedProfileGrade polynomialTensorGrade
        have hs : (∑ i : Fin d,
            (α i / 1) * ((profileNat (fun i => (z.1 i).1)) i : ℝ)) =
            ((∑ i : Fin d, (z.1 i).1.val : ℕ) : ℝ) := by
          simp [α, profileNat]
        rw [hs, Nat.floor_natCast]
      rw [hgrade]
      exact z.2
    · have hgrade : weightedProfileGrade α 1
          (profileNat (fun i => (z.1 i).1) : Fin d → ℕ) =
          polynomialTensorGrade z.1 := by
        unfold weightedProfileGrade polynomialTensorGrade
        have hs : (∑ i : Fin d,
            (α i / 1) * ((profileNat (fun i => (z.1 i).1)) i : ℝ)) =
            ((∑ i : Fin d, (z.1 i).1.val : ℕ) : ℝ) := by
          simp [α, profileNat]
        rw [hs, Nat.floor_natCast]
      have hz : polynomialTensorGrade z.1 ≤ N := by rw [← hgrade]; exact z.2
      exact hz
  rw [Fintype.card_congr heq]
  exact hcount M N

/-- On elementary source tensors, the actual tensor RL map into cube `L²`
is bounded by the product of the actual one-dimensional `L²` RL norms. -/
theorem fractionalTensorRLToL2_tensorSource_norm_le {d : ℕ} (β : ℝ)
    (hβ : 1/2 < β) (v : Fin d → AxisL2) :
    ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
      (tensorSource v)‖ ≤
      ∏ i : Fin d, ‖fractionalRLOnL2 β hβ (v i)‖ := by
  let F : Fin d → C(UnitInterval, ℝ) := fun i => fractionalRL β hβ (v i)
  change ‖cubeProfileToL2
    (fractionalTensorRL (fun _ : Fin d => β) (fun _ => hβ) (tensorSource v))‖ ≤ _
  have hsource : tensorSource v = productToCube d (productVector v) := rfl
  have hprofile : fractionalTensorRL (fun _ : Fin d => β) (fun _ => hβ)
      (productToCube d (productVector v)) = cubeProductProfile F := by
    ext t
    exact fractionalTensorRL_product _ _ v t
  rw [hsource, hprofile, cubeProfileToL2_cubeProduct]
  simpa [F, fractionalRLOnL2, ContinuousLinearMap.comp_apply] using
    (cube_productVector_norm_le (fun i => profileToL2 (F i)))

private def gradeProfileEquiv {d M g : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AxisL2) :
    {a : (∀ i : Fin d, GradedFrameIndex (U i) M) //
        ∑ i, (a i).1.val = g} ≃
      Σ s : {s : Fin d → Fin (M+1) // ∑ i, (s i).val = g},
        (∀ i : Fin d, GradeIndex (U i) (s.1 i).val) where
  toFun a := ⟨⟨fun i => (a.1 i).1, a.2⟩, fun i => (a.1 i).2⟩
  invFun z := ⟨(fun i => ⟨z.1.1 i, z.2 i⟩), by simpa using z.1.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact Sigma.eta (a.1 i)
  right_inv z := by
    cases z with
    | mk s fiber =>
      apply Sigma.ext (Subtype.ext rfl)
      exact HEq.rfl

private theorem gradeProfile_card_le {d M g : ℕ} (hd : 0 < d) :
    Fintype.card {s : Fin d → Fin (M+1) // ∑ i, (s i).val = g} ≤
      (g+1)^(d-1) := by
  classical
  let S : Finset (Fin d → ℕ) :=
    Finset.univ.image (fun v : Fin d → Fin (g+1) => fun i => (v i).val)
  let P := {s : Fin d → Fin (M+1) // ∑ i, (s i).val = g}
  let Q := {v : Fin d → ℕ // v ∈ S.filter (fun v => ∑ i, v i = g)}
  letI : Fintype Q := Fintype.ofFinset (S.filter (fun v => ∑ i, v i = g))
    (by intro v; rfl)
  let e : P → Q := fun s => ⟨(fun i => (s.1 i).val), by
    apply Finset.mem_filter.mpr
    have hsum : ∑ i : Fin d, (s.1 i).val = g := s.2
    have hcoord (i : Fin d) : (s.1 i).val ≤ g := by
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun j => (s.1 j).val) (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      rw [hsum] at hs
      exact hs
    refine ⟨?_, hsum⟩
    apply Finset.mem_image.mpr
    refine ⟨(fun i => ⟨(s.1 i).val, Nat.lt_succ_of_le (hcoord i)⟩),
      Finset.mem_univ _, ?_⟩
    rfl⟩
  have he : Function.Injective e := by
    intro s t h
    apply Subtype.ext
    funext i
    have hv := congrArg Subtype.val h
    exact Fin.ext (congrFun hv i)
  have hcard := Fintype.card_le_of_injective e he
  have hQ : Fintype.card Q =
      (S.filter (fun v => ∑ i, v i = g)).card := Fintype.card_coe _
  rw [hQ] at hcard
  exact hcard.trans (shape_grade_card_le_power_pred hd S g)

/-- Tensor trace on a fixed total-grade fibre factors into the scalar grade
traces. This is the actual `L²` RL operator on the cube, not a formal tensor
operator. -/
theorem fractionalTensor_grade_trace_le_of_axis_grade_trace
    {d M g : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 1/2 < β)
    (U : Fin d → ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 < ρ)
    (haxis : ∀ i g,
      (∑ j : GradeIndex (U i) g,
        ‖fractionalRLOnL2 β hβ (gradeFamily (U i) (hfinite i) g j)‖^2) ≤
          A * ρ^g) :
    (∑ a : {a : (∀ i : Fin d, GradedFrameIndex (U i) M) //
        ∑ i, (a i).1.val = g},
      ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
        (tensorFrame (fun i => gradedFrame (U i) (hfinite i) M) a.1)‖^2) ≤
      A^d * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by
  classical
  let Profile := {s : Fin d → Fin (M+1) // ∑ i, (s i).val = g}
  let Fiber (s : Profile) := ∀ i : Fin d, GradeIndex (U i) (s.1 i).val
  let coeff (s : Profile) (a : Fiber s) :=
    ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
      (tensorFrame (fun i => gradeFamily (U i) (hfinite i) (s.1 i).val) a)‖^2
  have hcoeff (s : Profile) (a : Fiber s) :
      coeff s a ≤ ∏ i : Fin d,
        ‖fractionalRLOnL2 β hβ
          (gradeFamily (U i) (hfinite i) (s.1 i).val (a i))‖^2 := by
    have hn := fractionalTensorRLToL2_tensorSource_norm_le β hβ
      (fun i => gradeFamily (U i) (hfinite i) (s.1 i).val (a i))
    dsimp [coeff]
    rw [show tensorFrame (fun i => gradeFamily (U i) (hfinite i)
        (s.1 i).val) a = tensorSource (fun i =>
          gradeFamily (U i) (hfinite i) (s.1 i).val (a i)) from rfl]
    have hprodnonneg : 0 ≤ ∏ i : Fin d,
        ‖fractionalRLOnL2 β hβ
          (gradeFamily (U i) (hfinite i) (s.1 i).val (a i))‖ :=
      Finset.prod_nonneg fun i hi => norm_nonneg _
    have hn2 := (sq_le_sq₀ (norm_nonneg _) hprodnonneg).2 hn
    simpa [Finset.prod_pow] using hn2
  have hprofile (s : Profile) :
      (∑ a : Fiber s, coeff s a) ≤ A^d * ρ^g := by
    have hbound : (∑ a : Fiber s, coeff s a) ≤
        ∏ i : Fin d, ∑ j : GradeIndex (U i) (s.1 i).val,
          ‖fractionalRLOnL2 β hβ
            (gradeFamily (U i) (hfinite i) (s.1 i).val j)‖^2 := by
      calc
        _ ≤ ∑ a : Fiber s, ∏ i : Fin d,
          ‖fractionalRLOnL2 β hβ
            (gradeFamily (U i) (hfinite i) (s.1 i).val (a i))‖^2 :=
              Finset.sum_le_sum (fun a ha => hcoeff s a)
        _ = ∑ a : Fiber s, (∏ i : Fin d,
          ‖fractionalRLOnL2 β hβ
            (gradeFamily (U i) (hfinite i) (s.1 i).val (a i))‖)^2 := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.prod_pow]
        _ = _ := AlignmentNestedProjectionTensor.sum_pi_prod_sq
          (J := fun i => GradeIndex (U i) (s.1 i).val)
          (c := fun i j => ‖fractionalRLOnL2 β hβ
            (gradeFamily (U i) (hfinite i) (s.1 i).val j)‖)
    have hfactor : ∀ i : Fin d,
      ∑ j : GradeIndex (U i) (s.1 i).val,
        ‖fractionalRLOnL2 β hβ
          (gradeFamily (U i) (hfinite i) (s.1 i).val j)‖^2 ≤
            A * ρ^((s.1 i).val) := fun i => haxis i (s.1 i).val
    calc
      _ ≤ ∏ i : Fin d, A * ρ^((s.1 i).val) := hbound.trans (by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Finset.sum_nonneg fun j hj => sq_nonneg _
        · intro i hi
          exact hfactor i)
      _ = A^d * ρ^g := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rw [show ∑ i : Fin d, (s.1 i).val = g from s.2]
        simp [Fintype.card_fin]
  have hsumEq :
      (∑ a : {a : (∀ i : Fin d, GradedFrameIndex (U i) M) //
          ∑ i, (a i).1.val = g},
        ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
          (tensorFrame (fun i => gradedFrame (U i) (hfinite i) M) a.1)‖^2) =
       ∑ s : Profile, ∑ a : Fiber s, coeff s a := by
    calc
      _ = ∑ z : (Σ s : Profile, Fiber s), coeff z.1 z.2 :=
        Fintype.sum_equiv (gradeProfileEquiv U) _ _ (by intro a; rfl)
      _ = _ := by rw [Fintype.sum_sigma]
  rw [hsumEq]
  calc
    _ ≤ ∑ s : Profile, A^d * ρ^g := Finset.sum_le_sum (fun s hs => hprofile s)
    _ = (Fintype.card Profile : ℝ) * (A^d * ρ^g) := by simp
    _ ≤ ((g+1:ℕ):ℝ)^(d-1) * (A^d * ρ^g) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast gradeProfile_card_le (d:=d) (M:=M) (g:=g) hd
    _ = A^d * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by ring

/-- The actual one-dimensional polynomial filtrations have a geometric trace
envelope on every grade. Grade zero and the first increment use the operator
norm; all later grades use the scalar kernel-residual trace budget. -/
theorem exists_fractionalRLOnL2_grade_trace_bound {β : ℝ}
    (hβ : 1/2 < β) :
    ∃ q : ℕ, ∃ A : ℝ, 0 < q ∧ 0 < A ∧
      ∀ g : ℕ,
        (∑ j : GradeIndex (piecewisePolynomials q) g,
          ‖fractionalRLOnL2 β hβ
            (gradeFamily (piecewisePolynomials q)
              (fun n => piecewisePolynomials_finiteDimensional q n) g j)‖^2) ≤
          A * (Real.rpow 2 (-(2*β-1)))^g := by
  obtain ⟨q,C,hq,hC,htrace⟩ := exists_increment_output_trace_bound hβ
  let U : ℕ → Submodule ℝ AxisL2 := piecewisePolynomials q
  let hfinite : ∀ n, FiniteDimensional ℝ ↥(U n) :=
    fun n => piecewisePolynomials_finiteDimensional q n
  let hnested : ∀ n, U n ≤ U (n+1) :=
    fun n => piecewisePolynomials_le_succ q n
  let T := fractionalRLOnL2 β hβ
  let ρ : ℝ := Real.rpow 2 (-(2*β-1))
  let A : ℝ := (3*(q:ℝ)*‖T‖^2 + C)/ρ + 1
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨q,A,hq,hApos,?_⟩
  intro g
  cases g with
  | zero =>
      letI := hfinite 0
      have hnorm (j : GradeIndex U 0) :
          ‖T (gradeFamily U hfinite 0 j)‖^2 ≤ ‖T‖^2 := by
        have hj : ‖gradeFamily U hfinite 0 j‖ = 1 := by
          have ho := (gradeFamily_orthonormal U hfinite 0).1 j
          simpa using ho
        calc
          _ ≤ (‖T‖ * ‖gradeFamily U hfinite 0 j‖)^2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact T.le_opNorm _
          _ = ‖T‖^2 := by rw [hj]; ring
      have hsum : (∑ j : GradeIndex U 0, ‖T (gradeFamily U hfinite 0 j)‖^2) ≤
          (Fintype.card (GradeIndex U 0):ℝ) * ‖T‖^2 := by
        calc
          _ ≤ ∑ _j : GradeIndex U 0, ‖T‖^2 :=
            Finset.sum_le_sum fun j hj => hnorm j
          _ = _ := by simp
      have hdimN : Fintype.card (GradeIndex U 0) ≤ q := by
        simpa [GradeIndex, U] using piecewisePolynomials_finrank_le q 0
      have hdim : (Fintype.card (GradeIndex U 0):ℝ) ≤ q := by exact_mod_cast hdimN
      have hbound : (∑ j : GradeIndex U 0,
          ‖T (gradeFamily U hfinite 0 j)‖^2) ≤ A := calc
        _ ≤ (Fintype.card (GradeIndex U 0):ℝ) * ‖T‖^2 := hsum
        _ ≤ (q:ℝ)*‖T‖^2 := mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
        _ ≤ A := by
          dsimp [A]
          have heq : ((3*(q:ℝ)*‖T‖^2+C)/ρ)*ρ = 3*(q:ℝ)*‖T‖^2+C := by
            field_simp
          have hq0 : 0 ≤ (q:ℝ)*‖T‖^2 := by positivity
          nlinarith
      simpa [ρ] using hbound
  | succ g =>
    cases g with
    | zero =>
      letI := hfinite 1
      have hnorm (j : GradeIndex U 1) :
          ‖T (gradeFamily U hfinite 1 j)‖^2 ≤ ‖T‖^2 := by
        have hj : ‖gradeFamily U hfinite 1 j‖ = 1 := by
          have ho := (gradeFamily_orthonormal U hfinite 1).1 j
          simpa using ho
        calc
          _ ≤ (‖T‖ * ‖gradeFamily U hfinite 1 j‖)^2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact T.le_opNorm _
          _ = ‖T‖^2 := by rw [hj]; ring
      have hsum : (∑ j : GradeIndex U 1, ‖T (gradeFamily U hfinite 1 j)‖^2) ≤
          (Fintype.card (GradeIndex U 1):ℝ) * ‖T‖^2 := by
        calc
          _ ≤ ∑ _j : GradeIndex U 1, ‖T‖^2 :=
            Finset.sum_le_sum fun j hj => hnorm j
          _ = _ := by simp
      have hdimN : Fintype.card (GradeIndex U 1) ≤ q*2 := by
        exact gradeIndex_card_le_of_growth U hfinite hnested
          (A:=q) (fun n => piecewisePolynomials_finrank_le q n) 1
      have hdim : (Fintype.card (GradeIndex U 1):ℝ) ≤ (q:ℝ)*2 := by exact_mod_cast hdimN
      have hpow : 0 ≤ ρ := hρ0.le
      have hbound : (∑ j : GradeIndex U 1,
          ‖T (gradeFamily U hfinite 1 j)‖^2) ≤ A*ρ := calc
        _ ≤ (Fintype.card (GradeIndex U 1):ℝ)*‖T‖^2 := hsum
        _ ≤ (q:ℝ)*2*‖T‖^2 := mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
        _ ≤ A*ρ := by
          dsimp [A]
          have heq : ((3*(q:ℝ)*‖T‖^2+C)/ρ)*ρ = 3*(q:ℝ)*‖T‖^2+C := by
            field_simp
          have hbase : 0 ≤ (q:ℝ)*‖T‖^2 := by positivity
          nlinarith
      simpa [ρ] using hbound
    | succ n =>
      have hN : 1 ≤ n+1 := by omega
      have ht := htrace (n+1) hN
      have hcast : (∑ j : GradeIndex U (n+2),
          ‖T (gradeFamily U hfinite (n+2) j)‖^2) ≤ C*ρ^(n+1) := by
        simpa [U,hfinite,T,ρ,GradeIndex,gradeFamily,incrementBasis,
          AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2] using ht
      have hρ : 0 < ρ := hρ0
      have hscale : C*ρ^(n+1) ≤ A*ρ^(n+2) := by
        have hnonneg : 0 ≤ 3*(q:ℝ)*‖T‖^2 := by positivity
        have hratio : C ≤ A*ρ := by
          dsimp [A]
          have heq : ((3*(q:ℝ)*‖T‖^2+C)/ρ)*ρ =
              3*(q:ℝ)*‖T‖^2+C := by field_simp
          rw [add_mul, heq]
          nlinarith [hρ0]
        calc
          C*ρ^(n+1) ≤ (A*ρ)*ρ^(n+1) :=
            mul_le_mul_of_nonneg_right hratio (pow_nonneg hρ.le (n+1))
          _ = A*ρ^(n+2) := by rw [pow_succ]; ring
      exact hcast.trans hscale

/-- The actual isotropic tensor RL map has the same geometric envelope on
each total-grade fibre.  The polynomial order and the envelope constants are
chosen once, independently of frame depth and grade. -/
theorem exists_fractionalTensor_grade_trace_bound_explicit {d : ℕ} (hd : 0 < d)
    {β : ℝ} (hβ : 1/2 < β) :
    ∃ q : ℕ, ∃ A ρ : ℝ, 0 < q ∧ 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ρ = Real.rpow 2 (-(2*β-1)) ∧
      ∀ M g : ℕ,
        (∑ a : {a : (∀ i : Fin d,
              GradedFrameIndex (piecewisePolynomials q) M) //
              ∑ i, (a i).1.val = g},
          ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
            (tensorFrame (fun i => gradedFrame (piecewisePolynomials q)
              (fun n => piecewisePolynomials_finiteDimensional q n) M) a.1)‖^2) ≤
        A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by
  obtain ⟨q,A,hq,hA,haxis⟩ := exists_fractionalRLOnL2_grade_trace_bound hβ
  let U : Fin d → ℕ → Submodule ℝ AxisL2 := fun _ => piecewisePolynomials q
  let hfinite : ∀ i n, FiniteDimensional ℝ (U i n) := fun _ n =>
    piecewisePolynomials_finiteDimensional q n
  let hnested : ∀ i n, U i n ≤ U i (n+1) := fun _ n =>
    piecewisePolynomials_le_succ q n
  let ρ : ℝ := Real.rpow 2 (-(2*β-1))
  let A' : ℝ := A^d
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have haxis' : ∀ i g,
      (∑ j : GradeIndex (U i) g,
        ‖fractionalRLOnL2 β hβ
          (gradeFamily (U i) (hfinite i) g j)‖^2) ≤ A * ρ^g := by
    intro i g
    simpa [U, ρ] using haxis g
  have htrace := fun M g =>
    fractionalTensor_grade_trace_le_of_axis_grade_trace hd β hβ U hfinite hnested
      (le_of_lt hA) hρ0 haxis' (M:=M) (g:=g)
  refine ⟨q,A',ρ,hq,?_,hρ0,hρ1,?_,?_⟩
  · dsimp [A']
    positivity
  · rfl
  · intro M g
    have h := htrace M g
    simpa only [U, A'] using h

/-- Compatibility wrapper retaining the original geometric-envelope API.
The stronger sibling `exists_fractionalTensor_grade_trace_bound_explicit`
also exposes the exact decay parameter used in the proof. -/
theorem exists_fractionalTensor_grade_trace_bound {d : ℕ} (hd : 0 < d)
    {β : ℝ} (hβ : 1/2 < β) :
    ∃ q : ℕ, ∃ A ρ : ℝ, 0 < q ∧ 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ M g : ℕ,
        (∑ a : {a : (∀ i : Fin d,
              GradedFrameIndex (piecewisePolynomials q) M) //
              ∑ i, (a i).1.val = g},
          ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
            (tensorFrame (fun i => gradedFrame (piecewisePolynomials q)
              (fun n => piecewisePolynomials_finiteDimensional q n) M) a.1)‖^2) ≤
        A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by
  obtain ⟨q,A,ρ,hq,hA,hρ0,hρ1,_hρeq,henergy⟩ :=
    exists_fractionalTensor_grade_trace_bound_explicit hd hβ
  exact ⟨q,A,ρ,hq,hA,hρ0,hρ1,henergy⟩

/-- All grades above a cutoff have uniformly bounded actual tensor-output
trace in every finite rectangular polynomial frame. -/
theorem fractionalTensor_grade_tail_le {d q M : ℕ} (hd : 0 < d)
    {β A ρ : ℝ} (hβ : 1/2 < β) (hA : 0 ≤ A)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (henergy : ∀ g : ℕ,
      (∑ a : {a : PolynomialTensorIndex d q M //
          polynomialTensorGrade a = g},
        fractionalTensorGradeCoefficient β hβ a.1) ≤
        A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g)
    (n : ℕ) :
    (∑ a ∈ Finset.univ.filter (fun a : PolynomialTensorIndex d q M =>
        n < polynomialTensorGrade a), fractionalTensorGradeCoefficient β hβ a) ≤
      A * ρ^n * ((n+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
  classical
  let I := PolynomialTensorIndex d q M
  let grade : I → ℕ := polynomialTensorGrade
  let coeff : I → ℝ := fractionalTensorGradeCoefficient β hβ
  have hgrade (a : I) : grade a < d*(M+1) := by
    dsimp [grade, polynomialTensorGrade]
    have hle : (∑ i : Fin d, (a i).1.val) ≤ ∑ _i : Fin d, M :=
      Finset.sum_le_sum fun i hi => Nat.le_of_lt_succ (a i).1.isLt
    have hlt : (∑ _i : Fin d, M) < ∑ _i : Fin d, (M+1) := by
      simp [hd]
    simpa using hle.trans_lt hlt
  have hcoeff (a : I) : 0 ≤ coeff a := by
    dsimp [coeff, fractionalTensorGradeCoefficient]
    positivity
  have henergy' (g : ℕ) :
      (∑ a : {a : I // grade a = g}, coeff a.1) ≤
        A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by
    simpa [I, grade, coeff, fractionalTensorGradeCoefficient,
      polynomialTensorGrade, polynomialTensorFrame] using henergy g
  exact finite_grade_profile_tail_le grade coeff hA hρ0 hρ1
    (L:=d*(M+1)) (k:=d-1) (C:=A) (q:=ρ) hgrade hcoeff henergy'

/-- Uniform high-grade Hilbert--Schmidt budget for the actual isotropic cube
RL operator on every rectangular polynomial frame. -/
theorem exists_fractionalTensor_grade_tail_bound {d : ℕ} (hd : 0 < d)
    {β : ℝ} (hβ : 1/2 < β) :
    ∃ q : ℕ, ∃ A ρ : ℝ, 0 < q ∧ 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ M n : ℕ,
        (∑ a ∈ Finset.univ.filter (fun a : PolynomialTensorIndex d q M =>
            n < polynomialTensorGrade a),
          fractionalTensorGradeCoefficient β hβ a) ≤
          A * ρ^n * ((n+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
  obtain ⟨q,A,ρ,hq,hA,hρ0,hρ1,henergy⟩ :=
    exists_fractionalTensor_grade_trace_bound hd hβ
  refine ⟨q,A,ρ,hq,hA,hρ0,hρ1,?_⟩
  intro M n
  exact fractionalTensor_grade_tail_le hd hβ hA.le hρ0 hρ1
    (fun g => henergy M g) n

/-- A finite rectangular polynomial frame refined by its low-total-grade
subframe.  The trace left after the low projection is exactly the high-grade
kernel trace, so it is uniformly controlled by the geometric tail estimate. -/
theorem polynomialTensor_low_refinement_data_of_card_bound {d q M N : ℕ}
    (hd : 2 ≤ d) (hq : 0 < q) (D : ℕ) (hD : 0 < D)
    (hDcard : ∀ M N,
      Fintype.card (PolynomialTensorLowIndex d q M N) ≤
        D * Fintype.card (LayerIndex d N)) {β A ρ : ℝ}
    (hβ : 1/2 < β) (hA : 0 ≤ A) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (henergy : ∀ g : ℕ,
      (∑ a : {a : PolynomialTensorIndex d q M // polynomialTensorGrade a = g},
        fractionalTensorGradeCoefficient β (by linarith [hβ]) a.1) ≤
          A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g) :
    ∃ (U V : Submodule ℝ (UnitCubeL2 d))
      (_hU : FiniteDimensional ℝ U) (_hV : FiniteDimensional ℝ V),
      U ≤ V ∧
      Module.rank ℝ (LinearMap.range
        (((fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => by linarith [hβ]) :
          UnitCubeL2 d →L[ℝ] UnitCubeL2 d).comp U.starProjection :
            UnitCubeL2 d →L[ℝ] UnitCubeL2 d) : UnitCubeL2 d →ₗ[ℝ] UnitCubeL2 d)) ≤
        (D * Fintype.card (LayerIndex d N) : Cardinal) ∧
      ∃ b : Fin (Module.finrank ℝ V) → V, Orthonormal ℝ b ∧
        (∑ i, ‖fractionalTensorRLToL2 (fun _ : Fin d => β)
          (fun _ => by linarith [hβ])
          ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
            ((V.subtypeₗᵢ : V →ₗᵢ[ℝ] UnitCubeL2 d) (b i)))‖^2) ≤
          A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) ∧
      U = polynomialTensorLowSpace (d:=d) (q:=q) (M:=M) (N:=N) ∧
      V = polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M) := by
  classical
  let hβ' : 1/2 < β := hβ
  let T : UnitCubeL2 d →L[ℝ] UnitCubeL2 d :=
    fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ')
  let V : Submodule ℝ (UnitCubeL2 d) :=
    polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)
  let U : Submodule ℝ (UnitCubeL2 d) :=
    polynomialTensorLowSpace (d:=d) (q:=q) (M:=M) (N:=N)
  letI hV : FiniteDimensional ℝ V := polynomialTensorRectangleSpace_finite
  letI hU : FiniteDimensional ℝ U := polynomialTensorLowSpace_finite
  have hUV : U ≤ V := polynomialTensorLowSpace_le_rectangle
  let frame : PolynomialTensorIndex d q M → UnitCubeL2 d := polynomialTensorFrame
  have hframe : Orthonormal ℝ frame := polynomialTensorFrame_orthonormal
  have hcard : Fintype.card (PolynomialTensorIndex d q M) =
      Module.finrank ℝ V := by
    change Fintype.card (PolynomialTensorIndex d q M) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range frame))
    rw [finrank_span_eq_card hframe.linearIndependent]
  have he : Fin (Module.finrank ℝ V) ≃ PolynomialTensorIndex d q M :=
    Fintype.equivOfCardEq (by simp [hcard])
  let b : Fin (Module.finrank ℝ V) → V := fun i =>
    ⟨frame (he i), Submodule.subset_span ⟨he i, rfl⟩⟩
  have hb : Orthonormal ℝ b := by
    have hb' := hframe.comp he he.injective
    change Orthonormal ℝ (fun i => (frame (he i) : UnitCubeL2 d))
    exact hb'
  have hdimU : Module.finrank ℝ U ≤ Fintype.card (PolynomialTensorLowIndex d q M N) := by
    let f : PolynomialTensorLowIndex d q M N → UnitCubeL2 d := fun a => frame a.1
    change Module.finrank ℝ (Submodule.span ℝ (Set.range f)) ≤ _
    calc
      _ ≤ (Set.range f).toFinset.card := finrank_span_le_card _
      _ ≤ Fintype.card (PolynomialTensorLowIndex d q M N) := by
        simpa only [Set.toFinset_card] using Fintype.card_range_le f
  have hDrank : Module.rank ℝ (LinearMap.range
      (((T.comp U.starProjection : UnitCubeL2 d →L[ℝ] UnitCubeL2 d) :
        UnitCubeL2 d →ₗ[ℝ] UnitCubeL2 d))) ≤ (D*Fintype.card (LayerIndex d N) : Cardinal) := by
    calc
      _ ≤ Module.rank ℝ (LinearMap.range
          (U.starProjection : UnitCubeL2 d →ₗ[ℝ] UnitCubeL2 d)) :=
            LinearMap.rank_comp_le_right _ _
      _ = Module.rank ℝ U := by rw [Submodule.range_starProjection]
      _ = (Module.finrank ℝ U : Cardinal) := by rw [← Module.finrank_eq_rank]
      _ ≤ (D*Fintype.card (LayerIndex d N) : Cardinal) := by
        exact_mod_cast hdimU.trans (hDcard M N)
  have horthLow (a : PolynomialTensorIndex d q M) (ha : N < polynomialTensorGrade a) :
      frame a ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    change y ∈ Submodule.span ℝ
      (Set.range fun z : PolynomialTensorLowIndex d q M N => frame z.1) at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro z ⟨z',rfl⟩
      have hne : a ≠ z'.1 := by
        intro heq
        have hgrade := congrArg polynomialTensorGrade heq
        rw [hgrade] at ha
        exact (Nat.not_lt_of_ge z'.2) ha
      have h := (orthonormal_iff_ite.mp hframe) a z'.1
      simpa [hne] using h
    · simp
    · intro y z hy hz hyz hzz
      rw [inner_add_right, hyz, hzz]
      simp
    · intro c y hy h
      rw [inner_smul_right, h]
      simp
  have hlowMem (a : PolynomialTensorIndex d q M)
      (ha : polynomialTensorGrade a ≤ N) : frame a ∈ U := by
    exact Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
  have hterm (a : PolynomialTensorIndex d q M) :
      ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection) (frame a))‖^2 =
        if N < polynomialTensorGrade a then
          fractionalTensorGradeCoefficient β hβ' a else 0 := by
    by_cases ha : N < polynomialTensorGrade a
    · have hp : U.starProjection (frame a) = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff (K := U)).2 (horthLow a ha)
      simp [ha, T, ContinuousLinearMap.sub_apply, hp, frame,
        fractionalTensorGradeCoefficient]
    · have hle : polynomialTensorGrade a ≤ N := Nat.le_of_not_gt ha
      have hp : U.starProjection (frame a) = frame a :=
        Submodule.starProjection_eq_self_iff.mpr (hlowMem a hle)
      simp [ha, T, ContinuousLinearMap.sub_apply, hp]
  have hsum : (∑ i : Fin (Module.finrank ℝ V),
      ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
        (b i : UnitCubeL2 d))‖^2) =
      ∑ a ∈ Finset.univ.filter (fun a : PolynomialTensorIndex d q M =>
        N < polynomialTensorGrade a), fractionalTensorGradeCoefficient β hβ' a := by
    rw [show (∑ i : Fin (Module.finrank ℝ V),
        ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
          (b i : UnitCubeL2 d))‖^2) =
        ∑ a : PolynomialTensorIndex d q M,
          ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
            (frame a))‖^2 from Fintype.sum_equiv he _ _ (by intro i; rfl)]
    simp_rw [hterm]
    rw [Finset.sum_filter]
  have htrace := fractionalTensor_grade_tail_le (by omega : 0 < d) hβ' (by positivity : 0 ≤ A)
    hρ0 hρ1 (fun g => henergy g) N
  refine ⟨U,V,hU,hV,hUV,hDrank,⟨b,hb,?_,rfl,rfl⟩⟩
  rw [show (∑ i, ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
        ((V.subtypeₗᵢ : V →ₗᵢ[ℝ] UnitCubeL2 d) (b i)))‖^2) =
        ∑ i : Fin (Module.finrank ℝ V),
        ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
          (b i : UnitCubeL2 d))‖^2 by rfl]
  rw [hsum]
  exact htrace

/-- Compatibility wrapper for the rank-bound form.  The stronger sibling
`polynomialTensor_low_refinement_data_of_card_bound` accepts a single global
rank multiplier, so it can be used uniformly while the cutoff and rectangle
depth vary. -/
theorem polynomialTensor_low_refinement_data {d q M N : ℕ}
    (hd : 2 ≤ d) (hq : 0 < q) {β A ρ : ℝ}
    (hβ : 1/2 < β) (hA : 0 ≤ A) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (henergy : ∀ g : ℕ,
      (∑ a : {a : PolynomialTensorIndex d q M // polynomialTensorGrade a = g},
        fractionalTensorGradeCoefficient β (by linarith [hβ]) a.1) ≤
          A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g) :
    ∃ D : ℕ, 0 < D ∧ ∃ (U V : Submodule ℝ (UnitCubeL2 d))
      (_hU : FiniteDimensional ℝ U) (_hV : FiniteDimensional ℝ V),
      U ≤ V ∧
      Module.rank ℝ (LinearMap.range
        (((fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => by linarith [hβ]) :
          UnitCubeL2 d →L[ℝ] UnitCubeL2 d).comp U.starProjection :
            UnitCubeL2 d →L[ℝ] UnitCubeL2 d) : UnitCubeL2 d →ₗ[ℝ] UnitCubeL2 d)) ≤
        (D * Fintype.card (LayerIndex d N) : Cardinal) ∧
      ∃ b : Fin (Module.finrank ℝ V) → V, Orthonormal ℝ b ∧
        (∑ i, ‖fractionalTensorRLToL2 (fun _ : Fin d => β)
          (fun _ => by linarith [hβ])
          ((ContinuousLinearMap.id ℝ (UnitCubeL2 d) - U.starProjection)
            ((V.subtypeₗᵢ : V →ₗᵢ[ℝ] UnitCubeL2 d) (b i)))‖^2) ≤
          A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
  obtain ⟨D,hD,hDcard⟩ := polynomialTensorLowIndex_card_le_layer_multiple
    (d:=d) (q:=q) hd hq
  obtain ⟨U,V,hU,hV,hUV,hRank,⟨b,hb,hTrace,_hUeq,_hVeq⟩⟩ :=
    polynomialTensor_low_refinement_data_of_card_bound
      (d:=d) (q:=q) (M:=M) (N:=N) hd hq D hD hDcard
      hβ hA hρ0 hρ1 henergy
  exact ⟨D,hD,U,V,hU,hV,hUV,hRank,⟨b,hb,hTrace⟩⟩

end BrownianSharp.AlignmentFractionalTensorL2TraceBudget
