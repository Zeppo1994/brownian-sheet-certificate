import BrownianSharp.AlignmentNestedProjectionTensorDecay
import BrownianSharp.AlignmentFractionalPolynomialBands
import BrownianSharp.AlignmentFractionalPaddingPermutation
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy
import BrownianSharp.AlignmentFractionalGenericGradeCounts
import Mathlib.Tactic

/-! Actual weighted grade-energy envelopes for tensor RL kernels using the
coordinatewise nested piecewise-polynomial filtrations. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000

namespace BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy

open BrownianSharp
open HaarQuarter
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionTensorDecay
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialBands
open BrownianSharp.AlignmentFractionalPadding
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy
open BrownianSharp.AlignmentFractionalGenericGradeCounts

abbrev PolynomialAxisL2 := AlignmentFractionalL2.UnitL2

private theorem exists_polynomial_axis_envelope {a : ℝ} (ha : 1/2 < a) :
    ∃ q : ℕ, ∃ A : ℝ, 0 < q ∧ 0 < A ∧ a-1+1/2 < (q:ℝ) ∧
      ∀ t : ℝ, ∀ ht0 : 0 ≤ t, ∀ ht1 : t ≤ 1, ∀ g : ℕ,
        (∑ j : GradeIndex (piecewisePolynomials q) g,
          ⟪kernelVector a t ha ht0 ht1,
            gradeFamily (piecewisePolynomials q) (fun n => inferInstance) g j⟫ ^ 2) ≤
          A * ((2:ℝ)^(-(2*a-1)))^g := by
  obtain ⟨q,hq⟩ := exists_nat_gt (a+1)
  have hqreal : (0:ℝ) < (q:ℝ) := by linarith
  have hqpos : 0 < q := by exact_mod_cast hqreal
  have horder : a-1+1/2 < (q:ℝ) := by linarith
  obtain ⟨A,hA,hbound⟩ := polynomialGrade_kernel_energy hqpos ha horder
  exact ⟨q,A,hqpos,hA,horder,by
    intro t ht0 ht1 g
    exact hbound t ht0 ht1 g⟩

private def polynomialFiltration {d : ℕ} (degree : Fin d → ℕ) :
    Fin d → ℕ → Submodule ℝ PolynomialAxisL2 :=
  fun i n => piecewisePolynomials (degree i) n

private theorem polynomialFiltration_finite {d : ℕ} (degree : Fin d → ℕ) :
    ∀ i n, FiniteDimensional ℝ ↥(polynomialFiltration degree i n) := by
  intro i n
  exact piecewisePolynomials_finiteDimensional (degree i) n

private theorem polynomialFiltration_nested {d : ℕ} (degree : Fin d → ℕ) :
    ∀ i n, polynomialFiltration degree i n ≤ polynomialFiltration degree i (n+1) := by
  intro i n
  exact piecewisePolynomials_le_succ (degree i) n

private theorem polynomialProfile_energy_le
    {d M : ℕ} (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d) (degree : Fin d → ℕ) (A : Fin d → ℝ)
    (hA : ∀ i, 0 ≤ A i)
    (hAxis : ∀ i, ∀ x : ℝ, ∀ hx0 : 0 ≤ x, ∀ hx1 : x ≤ 1, ∀ g,
      (∑ j : GradeIndex (piecewisePolynomials (degree i)) g,
        ⟪kernelVector (α i) x (hα i) hx0 hx1,
          gradeFamily (piecewisePolynomials (degree i)) (fun n => inferInstance) g j⟫ ^ 2) ≤
        A i * ((2:ℝ)^(-(2*α i-1)))^g)
    (s : Fin d → Fin (M+1)) :
    (∑ a : (∀ i, GradeIndex (polynomialFiltration degree i) (s i).val),
      ⟪tensorKernelFamily α hα t,
        tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
          (polynomialFiltration_finite degree i) M)
          (fun i => (⟨s i,a i⟩ : GradedFrameIndex
            (polynomialFiltration degree i) M))⟫ ^ 2) ≤
      ∏ i : Fin d, A i * ((2:ℝ)^(-(2*α i-1)))^(s i).val := by
  classical
  have haxis : ∀ i g,
      (∑ j : GradeIndex (polynomialFiltration degree i) g,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2,
          gradeFamily (polynomialFiltration degree i)
            (fun m => piecewisePolynomials_finiteDimensional (degree i) m) g j⟫ ^ 2) ≤
        A i * ((2:ℝ)^(-(2*α i-1)))^g := by
    intro i g
    change (∑ j : GradeIndex (piecewisePolynomials (degree i)) g,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2,
          gradeFamily (piecewisePolynomials (degree i))
            (fun m => piecewisePolynomials_finiteDimensional (degree i) m) g j⟫ ^ 2) ≤ _
    exact hAxis i (t.val i) (Set.mem_Icc.mp (t.property i)).1
      (Set.mem_Icc.mp (t.property i)).2 g
  exact tensorKernel_gradeProfile_energy_le
    (polynomialFiltration degree) (polynomialFiltration_finite degree)
    (polynomialFiltration_nested degree) α hα t A
    (fun i => (2:ℝ)^(-(2*α i-1))) hA
    (fun i => Real.rpow_nonneg (by norm_num) _) haxis s

/-- The actual tensor RL kernel has the sharp weighted grade energy envelope
for arbitrary order vectors with minimum multiplicity `ν`. The constant is
the product of coordinatewise envelopes obtained from genuine polynomial
projection estimates and is uniform in the truncation depth, anchor, and
weighted grade. -/
theorem polynomialTensor_weightedGrade_energy_le
    {ν e : ℕ} (hν : 0 < ν) (r : ℝ) (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ ep : Fin (ν+e) ≃ Fin (ν+e), ∃ w : Fin e → ℝ,
    ∃ degree : Fin (ν+e) → ℕ, ∃ A : Fin (ν+e) → ℝ,
      (∀ j : Fin e, 1 < w j) ∧
      (∀ i : Fin ν, α (ep (Fin.castAdd e i)) = r) ∧
      (∀ j : Fin e, α (ep (Fin.natAdd ν j)) = r*w j) ∧
      (∀ i, 0 < degree i) ∧ (∀ i, 0 < A i) ∧
      ∀ (M n : ℕ) (t : BrownianCubeAnchor (ν+e)),
      (∑ a : {a : ∀ i, GradedFrameIndex (polynomialFiltration degree i) M //
          weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
        ⟪tensorKernelFamily α hα t,
          tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
            (polynomialFiltration_finite degree i) M) a.1⟫ ^ 2) ≤
        (∏ i : Fin (ν+e), A i) *
          (Real.rpow 2 (-(2*r-1)*n) * (((n+1:ℕ):ℝ)^(ν-1) *
            ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
  classical
  obtain ⟨hmin, hmult⟩ := hm
  let ep := minimumCoordinatePermutation α r hmult
  let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ (by linarith : 0 < r)]
    exact minimumCoordinatePermutation_inactive_lt α r hmult hmin j
  have hpad : reindexOrders ep α =
      paddedOrders r (fun j => r*w j) := by
    dsimp [ep, w]
    exact minimumCoordinatePermutation_eq_padded α r hmult
      (ne_of_gt (by linarith : 0 < r)) hmin
  choose degree A hdegree hA horder hAxis using
    (fun i : Fin (ν+e) => exists_polynomial_axis_envelope (hα i))
  refine ⟨ep,w,degree,A,hw,?_,?_,hdegree,hA,?_⟩
  · intro i
    exact minimumCoordinatePermutation_first α r hmult i
  · intro j
    dsimp [w]
    field_simp [ne_of_gt (by linarith : 0 < r)]
  intro M n t
  let U := polynomialFiltration degree
  let rho : Fin (ν+e) → ℝ := fun i => (2:ℝ)^(-(2*α i-1))
  let PF : Type := {s : HaarGradeProfileBox (ν+e) M //
    weightedProfileGrade α r (profileNat s) = n}
  let PF' : Type := {s : HaarGradeProfileBox (ν+e) M //
    weightedProfileGrade (paddedOrders r (fun j => r*w j)) r (profileNat s) = n}
  let permuteFiber : PF ≃ PF' := {
    toFun := fun s => ⟨permuteHaarProfileEquiv ep s.1, by
      rw [← hpad]
      exact (weightedProfileGrade_reindex ep α r s.1).trans s.2⟩
    invFun := fun s => ⟨permuteHaarProfileEquiv ep.symm s.1, by
      have hs : weightedProfileGrade (reindexOrders ep α) r (profileNat s.1) = n := by
        rw [hpad]
        exact s.2
      simpa [reindexOrders_symm] using
        (weightedProfileGrade_reindex ep.symm (reindexOrders ep α) r s.1).trans hs⟩
    left_inv := by
      intro s
      apply Subtype.ext
      funext i
      simp [permuteHaarProfileEquiv]
    right_inv := by
      intro s
      apply Subtype.ext
      funext i
      simp [permuteHaarProfileEquiv]
  }
  let splitFiber := weightedProfileSplitEquiv (ν := ν) (e := e) (M := M)
    (n := n) (r := r) (ne_of_gt (by linarith : 0 < r)) w
  let Aprod := ∏ i : Fin (ν+e), A i
  have hAprod : 0 ≤ Aprod := by
    dsimp [Aprod]
    exact Finset.prod_nonneg fun i hi => (hA i).le
  have hsum_reindex :
      (∑ a : {a : ∀ i, GradedFrameIndex (U i) M //
          weightedProfileGrade α r (profileNat (fun i => (a i).1)) = n},
        ⟪tensorKernelFamily α hα t,
          tensorFrame (fun i => gradedFrame (U i) (polynomialFiltration_finite degree i) M)
            a.1⟫ ^ 2) =
      ∑ s : PF, ∑ a : AlignmentFractionalGenericGradeCounts.ProductGradeFiber U s.1,
        ⟪tensorKernelFamily α hα t,
          tensorFrame (fun i => gradedFrame (U i) (polynomialFiltration_finite degree i) M)
            (fun i => (⟨s.1 i,a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 := by
    calc
      _ = ∑ x : (Σ s : PF, AlignmentFractionalGenericGradeCounts.ProductGradeFiber U s.1),
          ⟪tensorKernelFamily α hα t,
            tensorFrame (fun i => gradedFrame (U i) (polynomialFiltration_finite degree i) M)
              (fun i => (⟨x.1.1 i,x.2 i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 :=
            Fintype.sum_equiv
              (AlignmentFractionalGenericGradeCounts.productGradeFiberEquiv U α r)
              _ _ (by intro a; rfl)
      _ = _ := by rw [Fintype.sum_sigma]
  have hprofile (s : HaarGradeProfileBox (ν+e) M) :
      (∑ a : AlignmentFractionalGenericGradeCounts.ProductGradeFiber U s,
        ⟪tensorKernelFamily α hα t,
          tensorFrame (fun i => gradedFrame (U i) (polynomialFiltration_finite degree i) M)
            (fun i => (⟨s i,a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2) ≤
      ∏ i : Fin (ν+e), A i * rho i^(s i).val := by
      simpa [U, rho, AlignmentFractionalGenericGradeCounts.ProductGradeFiber] using
      polynomialProfile_energy_le α hα t degree A
        (fun i => (hA i).le)
        (fun i x hx0 hx1 g => hAxis i x hx0 hx1 g) s
  have hactive (i : Fin ν) : α (ep (Fin.castAdd e i)) = r := by
    exact minimumCoordinatePermutation_first α r hmult i
  have hinactive (j : Fin e) : α (ep (Fin.natAdd ν j)) = r*w j := by
    dsimp [w]
    field_simp [ne_of_gt (by linarith : 0 < r)]
  have hweighted_sum :
      (∑ s : PF, ∏ i : Fin (ν+e), A i * rho i^(profileNat s.1 i)) =
        Aprod *
          ∑ p : {p : ActiveBox ν M × InactiveBox e M //
              weightedGradeFloor w p.1 p.2 = n},
            (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
              ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := by
    calc
      _ = Aprod * ∑ s : PF, ∏ i : Fin (ν+e), rho i^(profileNat s.1 i) := by
        rw [show (∑ s : PF, ∏ i : Fin (ν+e), A i * rho i^(profileNat s.1 i)) =
          ∑ s : PF, Aprod * ∏ i : Fin (ν+e), rho i^(profileNat s.1 i) by
            apply Finset.sum_congr rfl
            intro s hs
            simp [Aprod, Finset.prod_mul_distrib]]
        rw [Finset.mul_sum]
      _ = Aprod * ∑ s : PF', ∏ j : Fin (ν+e),
            rho (ep j)^(profileNat s.1 j) := by
        congr 1
        exact Fintype.sum_equiv permuteFiber _ _ (by
          intro s
          change (∏ i : Fin (ν+e), rho i^(profileNat s.1 i)) = _
          exact Fintype.prod_equiv ep.symm _ _ (by
            intro i
            simp [profileNat, permuteFiber, permuteHaarProfileEquiv]))
      _ = Aprod * ∑ p : {p : ActiveBox ν M × InactiveBox e M //
            weightedGradeFloor w p.1 p.2 = n},
            (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
              ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := by
        congr 1
        exact Fintype.sum_equiv splitFiber _ _ (by
          intro s
          let p := (splitFiber s).1
          calc
            _ = (∏ i : Fin ν, rho (ep (Fin.castAdd e i))^
                  (s.1 (Fin.castAdd e i)).val) *
                ∏ j : Fin e, rho (ep (Fin.natAdd ν j))^
                  (s.1 (Fin.natAdd ν j)).val := by
                  calc
                    _ = ∏ x : Fin ν ⊕ Fin e,
                        rho (ep (finSumFinEquiv x))^
                          (s.1 (finSumFinEquiv x)).val := by
                        symm
                        exact Fintype.prod_equiv finSumFinEquiv _ _ (by intro x; rfl)
                    _ = _ := by
                      rw [Fintype.prod_sum_type]
                      simp [finSumFinEquiv]
            _ = (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1 i).val) *
                ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.2 j).val := by
                  congr 1
                  · apply Finset.prod_congr rfl
                    intro i hi
                    have hp' : p.1 i = s.1 (Fin.castAdd e i) := by
                      change (splitHaarProfileEquiv s.1).1 i = s.1 (Fin.castAdd e i)
                      rfl
                    rw [← hp']
                    simp [rho, hactive i]
                  · apply Finset.prod_congr rfl
                    intro j hj
                    have hp' : p.2 j = s.1 (Fin.natAdd ν j) := by
                      change (splitHaarProfileEquiv s.1).2 j = s.1 (Fin.natAdd ν j)
                      rfl
                    rw [← hp']
                    simp [rho, hinactive j]
                    ring)
  have hbox :
      (∑ p : {p : ActiveBox ν M × InactiveBox e M //
          weightedGradeFloor w p.1 p.2 = n},
        Aprod * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
          ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val)) ≤
        Aprod * (Real.rpow 2 (-(2*r-1)*n) * (((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
    exact weighted_box_profile_subtype_energy_le hν hr hAprod w hw
  rw [hsum_reindex]
  calc
    _ ≤ ∑ s : PF, ∏ i : Fin (ν+e), A i * rho i^(profileNat s.1 i) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hprofile s.1
    _ = Aprod * ∑ p : {p : ActiveBox ν M × InactiveBox e M //
          weightedGradeFloor w p.1 p.2 = n},
        (∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
          ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val := hweighted_sum
    _ ≤ Aprod * (Real.rpow 2 (-(2*r-1)*n) * (((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
      rw [Finset.mul_sum]
      exact hbox

end BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
