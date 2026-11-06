import BrownianSharp.AlignmentPaperMaternGradedTensor
import BrownianSharp.AlignmentPaperMaternHolder
import BrownianSharp.BrownianCubeSpan
import BrownianSharp.AlignmentGaussianGradedKernelReverse
import BrownianSharp.AlignmentGaussianGradedFeatureVariance
import BrownianSharp.AlignmentFractionalSheetGradedFrame
import BrownianSharp.AlignmentFractionalGenericGradeCounts
import BrownianSharp.AlignmentAuditHaarDilationBudget
import BrownianSharp.AlignmentUniformGeometricApproximation
import BrownianSharp.AlignmentPaperMatern
import BrownianSharp.AlignmentPaperMaternFinal
import BrownianSharp.AlignmentPaperMaternSpectralAggregation
import Mathlib.Tactic

/-! Actual tensor-grade energy, fiber counts, and uniform-frame inputs for the
Matérn graded Gaussian reverse argument. The analytic input to the axis-energy
lemma is only the scalar projection residual; the Matérn cell approximation
route discharges it. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternGradedReverse

open BrownianSharp.AlignmentPaperMaternGradedTensor
open BrownianSharp.AlignmentPaperMaternHolder
open BrownianSharp.AlignmentMaternContinuousFeature
open BrownianSharp.AlignmentPaperMaternSpectralAggregation
open BrownianSharp.AlignmentMaternTensorFeature
open BrownianSharp.AlignmentFractionalPadding
open BrownianSharp.AlignmentPaperMaternSpectralFiltration
open BrownianSharp.AlignmentPaperMaternSpectralApproximation
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalGenericGradeCounts
open BrownianSharp.AlignmentFractionalSheetGradedFrame
open BrownianSharp.AlignmentGaussianGradedFeatureVariance
open BrownianSharp.AlignmentGaussianGradedKernelReverse
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentMaternContinuousFeature

/-- The actual coordinate filtration used by the tensor Matérn frame. -/
abbrev AxisFiltration {d : ℕ} (κ : Fin d → ℝ) (h : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∀ i : Fin d, ℕ → Submodule ℝ (SpectralAxisL2 (κ i) h) :=
  axisFiltration κ h q hκ hh

/-- Squared coefficient energy on a single actual Matérn coordinate grade.
This is derived from the genuine cumulative-space projection residual. -/
theorem axisGradeEnergy_le_of_projection_residual {d : ℕ}
    (κ : Fin d → ℝ) (h hdecay : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h t (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h t (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∀ i (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ g,
      (∑ j : GradeIndex (AxisFiltration κ h q hκ hh i) g,
        ⟪normalizedAxis (κ i) h t (hκ i) hh,
          gradeFamily (AxisFiltration κ h q hκ hh i)
            (fun N => cumulativeLevelSpace_finiteDimensional (κ i) h q N (hκ i) hh)
            g j⟫ ^ 2) ≤
        (1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2) *
          ((Real.rpow 2 (-hdecay)) ^ 2) ^ g := by
  intro i t ht0 ht1 g
  have haxis := cumulativeGradeEnergy_le_of_projection_residual
    (κ i) h q (hκ i) hh
    (fun _ : Unit => normalizedAxis (κ i) h t (hκ i) hh)
    1 (Cres i) hdecay (by norm_num) (hCres i)
    (by intro _; rw [normalizedAxis_norm]; norm_num)
    (by intro _ N; exact hres i t ht0 ht1 N)
  change (∑ j : GradeIndex (cumulativeFiltrationFamily (κ i) h q
      (hκ i) hh) g,
        ⟪normalizedAxis (κ i) h t (hκ i) hh,
          gradeFamily (cumulativeFiltrationFamily (κ i) h q
            (hκ i) hh)
            (fun N => cumulativeLevelSpace_finiteDimensional (κ i) h q N
              (hκ i) hh) g j⟫^2) ≤ _
  exact haxis () g

/-- The scalar Matérn holder estimate gives the squared increment input for
all finite tensor frames, since orthonormal projection cannot increase norm. -/
theorem tensorFrame_increment_le_holder {d M : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (a b : BrownianCubeAnchor d) :
    ∑ u : (∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
      (⟪maternSheetFeature κ h hκ hh a, tensorGradedFrame κ h q hκ hh u⟫ -
        ⟪maternSheetFeature κ h hκ hh b, tensorGradedFrame κ h q hκ hh u⟫) ^ 2 ≤
      (‖maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b‖) ^ 2 := by
  classical
  have horth := tensorGradedFrame_orthonormal κ h q hκ hh (M := M)
  have hbessel := horth.sum_inner_products_le (s := Finset.univ)
    (maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b)
  have hsum : (∑ u : (∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
      (⟪maternSheetFeature κ h hκ hh a, tensorGradedFrame κ h q hκ hh u⟫ -
        ⟪maternSheetFeature κ h hκ hh b, tensorGradedFrame κ h q hκ hh u⟫) ^ 2) =
      ∑ u : (∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
        ⟪tensorGradedFrame κ h q hκ hh u,
          maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b⟫ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    have hinner :
        ⟪maternSheetFeature κ h hκ hh a, tensorGradedFrame κ h q hκ hh u⟫ -
          ⟪maternSheetFeature κ h hκ hh b, tensorGradedFrame κ h q hκ hh u⟫ =
        ⟪tensorGradedFrame κ h q hκ hh u,
          maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b⟫ := by
      calc
        _ = ⟪tensorGradedFrame κ h q hκ hh u,
              maternSheetFeature κ h hκ hh a⟫ -
            ⟪tensorGradedFrame κ h q hκ hh u,
              maternSheetFeature κ h hκ hh b⟫ := by
          rw [real_inner_comm (tensorGradedFrame κ h q hκ hh u)
                (maternSheetFeature κ h hκ hh a),
              real_inner_comm (tensorGradedFrame κ h q hκ hh u)
                (maternSheetFeature κ h hκ hh b)]
        _ = _ := by rw [inner_sub_right]
    rw [hinner]
  calc
    _ = ∑ u : (∀ i : Fin d,
          GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
          ⟪tensorGradedFrame κ h q hκ hh u,
            maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b⟫ ^ 2 := hsum
    _ ≤ ‖maternSheetFeature κ h hκ hh a - maternSheetFeature κ h hκ hh b‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using hbessel

/-- Finite tensor frame rank in each coordinate grade. -/
theorem axisGrade_card_le (d : ℕ) (κ : Fin d → ℝ) (h : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∀ i g, Fintype.card (GradeIndex (AxisFiltration κ h q hκ hh i) g) ≤
      (18*q) * 2^g := by
  intro i g
  have hgrowth := cumulativeLevelSpace_finrank_le (κ i) h q
    g (hκ i) hh
  have hdim : ∀ n, Module.finrank ℝ
      ↥(AxisFiltration κ h q hκ hh i n) ≤ (18*q)*2^n := by
    intro n
    exact cumulativeLevelSpace_finrank_le (κ i) h q n (hκ i) hh
  exact gradeIndex_card_le_of_growth (AxisFiltration κ h q hκ hh i)
    (fun n => cumulativeLevelSpace_finiteDimensional (κ i) h q n (hκ i) hh)
    (fun n => cumulativeLevelSpace_nested (κ i) h q n (hκ i) hh)
    hdim g

private theorem sum_pi_prod_sq {d : ℕ} (J : Fin d → Type*) [∀ i, Fintype (J i)]
    (c : ∀ i, J i → ℝ) :
    (∑ x : (∀ i, J i), (∏ i, c i (x i)) ^ 2) =
      ∏ i : Fin d, ∑ j : J i, c i j ^ 2 := by
  classical
  have hpow (x : ∀ i, J i) :
      (∏ i : Fin d, c i (x i)) ^ 2 = ∏ i : Fin d, c i (x i) ^ 2 := by
    simpa using (Finset.prod_pow (Finset.univ : Finset (Fin d)) 2
      (fun i => c i (x i))).symm
  simp_rw [hpow]
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (J i))) (fun i j => c i j ^ 2)).symm

/-- Actual Matérn tensor coefficients factor exactly on each product grade
profile; each factor is bounded by the scalar cumulative-projection energy. -/
theorem maternTensor_profileEnergy_le {d M : ℕ}
    (κ : Fin d → ℝ) (h hdecay : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h x (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h x (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N)
    (t : BrownianCubeAnchor d) (M : ℕ)
    (s : HaarGradeProfileBox d M) :
    (∑ a : (∀ i : Fin d,
        GradeIndex (AxisFiltration κ h q hκ hh i) (s i).val),
      ⟪maternSheetFeature κ h hκ hh t,
        tensorGradedFrame κ h q hκ hh
          (fun i => (⟨s i, a i⟩ :
            GradedFrameIndex (AxisFiltration κ h q hκ hh i) M))⟫ ^ 2) ≤
      ∏ i : Fin d,
        (1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2) *
          ((Real.rpow 2 (-hdecay)) ^ 2) ^ (s i).val := by
  classical
  let U := AxisFiltration κ h q hκ hh
  let J : Fin d → Type := fun i => GradeIndex (U i) (s i).val
  let c : ∀ i, J i → ℝ := fun i a =>
    ⟪normalizedAxis (κ i) h (t.val i) (hκ i) hh,
      gradeFamily (U i)
        (fun N => cumulativeLevelSpace_finiteDimensional (κ i) h q N (hκ i) hh)
        (s i).val a⟫
  have hfactor :
      (∑ a : (∀ i : Fin d, GradeIndex (U i) (s i).val),
        ⟪maternSheetFeature κ h hκ hh t,
          tensorGradedFrame κ h q hκ hh
            (fun i => (⟨s i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2) =
        ∏ i : Fin d, ∑ j : J i, c i j ^ 2 := by
    calc
      _ = ∑ a : (∀ i, J i), (∏ i, c i (a i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [maternSheetFeature_inner_tensorGradedFrame]
        congr 1
      _ = _ := sum_pi_prod_sq J c
  rw [hfactor]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun a ha => sq_nonneg _
  · intro i hi
    have hcoord := axisGradeEnergy_le_of_projection_residual
      κ h hdecay q hκ hh hdecay_pos Cres hCres hres
    have ht : 0 ≤ t.val i ∧ t.val i ≤ 1 := Set.mem_Icc.mp (t.property i)
    have haxis := hcoord i (t.val i) ht.1 ht.2 (s i).val
    change (∑ j : J i, c i j ^ 2) ≤ _
    exact haxis

/-- The sum of the coordinate grades is the weighted-profile grade with unit
weights. This lets the actual total-grade fiber use the generic profile
partition and its dimension-only composition bound. -/
def maternTensorGrade {d M : ℕ} (κ : Fin d → ℝ) (h r : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (u : ∀ i : Fin d,
      GradedFrameIndex (AxisFiltration κ h q hκ hh i) M) : ℕ :=
  weightedProfileGrade (fun _ : Fin d => r) r
    (profileNat (fun i => (u i).1))

/-- The number of finite grade profiles with total grade `n` is bounded by
the weak-composition polynomial, independently of truncation depth. -/
theorem maternProfile_card_le {d M : ℕ} (hd : 0 < d) (r : ℝ)
    (hr : 1/2 < r) (n : ℕ) :
    (Fintype.card {s : HaarGradeProfileBox d M //
      weightedProfileGrade (fun _ : Fin d => r) r (profileNat s) = n} : ℝ) ≤
      2 * (((n+1:ℕ):ℝ)^(d-1)) := by
  let w : Fin 0 → ℝ := fun j => Fin.elim0 j
  let α : Fin d → ℝ := paddedOrders r (fun j : Fin 0 => r * w j)
  have hα : α = (fun _ : Fin d => r) := by
    funext i
    change ((finSumFinEquiv (m := d) (n := 0)).symm
      (Fin.castAdd 0 i)).elim (fun _ => r) (fun j => r * w j) = r
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have hsum := paddedProfile_dimension_sum_le
    (M := M) (n := n) (r := r) (w := w)
    (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1/2) hr))
    (by intro j; exact Fin.elim0 j) hd
  have hsum' :
      (∑ s : {s : HaarGradeProfileBox d M //
          weightedProfileGrade α r (profileNat s) = n},
        (2:ℝ)^(∑ i : Fin d, (profileNat s.1 i : ℕ))) ≤
        Real.rpow 2 (n+1) * (((n+1:ℕ):ℝ)^(d-1)) := by
    simpa [α, w, paddedOrders, Finset.prod_empty] using hsum
  let S := {s : HaarGradeProfileBox d M //
      weightedProfileGrade α r (profileNat s) = n}
  have hgrade (s : S) : (∑ i : Fin d, (profileNat s.1 i : ℕ)) = n := by
    have hrpos : 0 < r := lt_trans (by norm_num : (0:ℝ) < 1/2) hr
    have hfloor : Nat.floor (∑ i : Fin d, (profileNat s.1 i : ℝ)) = n := by
      simpa [S, weightedProfileGrade, profileNat, div_self hrpos.ne', hα] using s.2
    have hcast : (∑ i : Fin d, (profileNat s.1 i : ℝ)) =
        ((∑ i : Fin d, profileNat s.1 i : ℕ) : ℝ) := by norm_cast
    rw [hcast, Nat.floor_natCast] at hfloor
    exact hfloor
  have hsumconst :
      (∑ s : S, (2:ℝ)^(∑ i : Fin d, (profileNat s.1 i : ℕ))) =
        (Fintype.card S : ℝ) * (2:ℝ)^n := by
    calc
      _ = ∑ _s : S, (2:ℝ)^n := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hgrade s]
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hbound : (Fintype.card S : ℝ)*(2:ℝ)^n ≤
      Real.rpow 2 (n+1) * (((n+1:ℕ):ℝ)^(d-1)) := by
    calc
      _ = ∑ s : S, (2:ℝ)^(∑ i : Fin d, (profileNat s.1 i : ℕ)) := hsumconst.symm
      _ ≤ _ := hsum'
  have htwo : Real.rpow 2 (n+1) = (2:ℝ)^n * 2 := by
    have hexp : (n:ℝ) + 1 = ((n+1:ℕ):ℝ) := by norm_cast
    rw [hexp]
    have hrpow : Real.rpow 2 ((n+1:ℕ):ℝ) = (2:ℝ)^(n+1) := by
      exact Real.rpow_natCast 2 (n+1)
    rw [hrpow, pow_succ]
  have hbound' : (Fintype.card S : ℝ)*(2:ℝ)^n ≤
      (2:ℝ)^n * (2 * (((n+1:ℕ):ℝ)^(d-1))) := by
    rw [htwo] at hbound
    nlinarith [hbound]
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hbound'' : (2:ℝ)^n * (Fintype.card S : ℝ) ≤
      (2:ℝ)^n * (2 * (((n+1:ℕ):ℝ)^(d-1))) := by
    simpa [mul_comm] using hbound'
  have hcard : (Fintype.card S : ℝ) ≤ 2 * (((n+1:ℕ):ℝ)^(d-1)) :=
    (mul_le_mul_iff_right₀ hpow).mp hbound''
  simpa [S, α, hα] using hcard

/-- Sum the profile energy over the actual total-grade fiber. This is the
`2^{-2h n}(n+1)^{d-1}` coefficient-energy envelope needed by the Gaussian
reverse theorem. -/
theorem maternTensor_totalGradeEnergy_le {d M : ℕ} (hd : 0 < d)
    (κ : Fin d → ℝ) (h hdecay r : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (hr : 1/2 < r) (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h x (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h x (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∀ t : BrownianCubeAnchor d, ∀ n : ℕ,
      (∑ u : {u : ∀ i : Fin d,
          GradedFrameIndex (AxisFiltration κ h q hκ hh i) M //
          maternTensorGrade κ h r q hκ hh u = n},
        ⟪maternSheetFeature κ h hκ hh t,
          tensorGradedFrame κ h q hκ hh u.1⟫ ^ 2) ≤
        (2 * ∏ i : Fin d,
          (1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2)) *
          ((Real.rpow 2 (-hdecay)) ^ 2) ^ n * (((n+1:ℕ):ℝ)^(d-1)) := by
  intro t n
  let U := AxisFiltration κ h q hκ hh
  let α : Fin d → ℝ := fun _ => r
  let prof := {s : HaarGradeProfileBox d M //
    weightedProfileGrade α r (profileNat s) = n}
  let fib := {u : ∀ i : Fin d, GradedFrameIndex (U i) M //
    weightedProfileGrade α r (profileNat (fun i => (u i).1)) = n}
  have hsumNat (s : prof) :
      (∑ i : Fin d, (profileNat s.1 i : ℕ)) = n := by
    have hrpos : 0 < r := lt_trans (by norm_num : (0:ℝ) < 1/2) hr
    have hfloor : Nat.floor (∑ i : Fin d, (profileNat s.1 i : ℝ)) = n := by
      simpa [prof, weightedProfileGrade, α, profileNat, div_self hrpos.ne'] using s.2
    have hcast : (∑ i : Fin d, (profileNat s.1 i : ℝ)) =
        ((∑ i : Fin d, profileNat s.1 i : ℕ) : ℝ) := by norm_cast
    rw [hcast, Nat.floor_natCast] at hfloor
    exact hfloor
  let Fiber (s : prof) := ∀ i : Fin d, GradeIndex (U i) (s.1 i).val
  let equiv : fib ≃ Σ s : prof, Fiber s := {
    toFun := fun u => ⟨⟨fun i => (u.1 i).1, u.2⟩, fun i => (u.1 i).2⟩
    invFun := fun z => ⟨(fun i => ⟨z.1.1 i, z.2 i⟩), z.1.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      funext i
      exact Sigma.eta (u.1 i)
    right_inv := by
      intro z
      cases z with
      | mk s fiber =>
        apply Sigma.ext (Subtype.ext rfl)
        exact HEq.rfl }
  have hfiberSum :
      (∑ u : fib, ⟪maternSheetFeature κ h hκ hh t,
          tensorGradedFrame κ h q hκ hh u.1⟫ ^ 2) =
        ∑ z : Σ s : prof, Fiber s,
          ⟪maternSheetFeature κ h hκ hh t,
            tensorGradedFrame κ h q hκ hh
              (fun i => (⟨z.1.1 i, z.2 i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2 := by
    exact Fintype.sum_equiv equiv _ _ (by intro u; rfl)
  change (∑ u : fib, ⟪maternSheetFeature κ h hκ hh t,
      tensorGradedFrame κ h q hκ hh u.1⟫ ^ 2) ≤ _
  rw [hfiberSum]
  rw [Fintype.sum_sigma]
  let B : Fin d → ℝ := fun i =>
    1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2
  let q0 : ℝ := (Real.rpow 2 (-hdecay)) ^ 2
  have hB : ∀ i, 0 ≤ B i := by
    intro i
    dsimp [B]
    positivity
  have hq0 : 0 < q0 := by
    dsimp [q0]
    positivity
  have hprodB : 0 ≤ ∏ i : Fin d, B i :=
    Finset.prod_nonneg fun i hi => hB i
  have hprofiles := maternProfile_card_le (M := M) hd r hr n
  have hprofiles' : (Fintype.card prof : ℝ) ≤
      2 * (((n+1:ℕ):ℝ)^(d-1)) := by
    simpa [prof, α] using hprofiles
  have hprofileBound (s : prof) :
      ∏ i : Fin d, B i * q0^(s.1 i).val =
        (∏ i : Fin d, B i) * q0^n := by
    calc
      _ = (∏ i : Fin d, B i) *
          (∏ i : Fin d, q0^(s.1 i).val) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ i : Fin d, B i) * q0^(∑ i : Fin d, (s.1 i).val) := by
            rw [← Finset.prod_pow_eq_pow_sum]
      _ = _ := by
        have hsumNat' : (∑ i : Fin d, (s.1 i).val) = n := by
          simpa [profileNat] using hsumNat s
        rw [hsumNat']
  calc
    _ ≤ ∑ s : prof, (∏ i : Fin d, B i) * q0^n := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        _ ≤ ∏ i : Fin d, B i * q0^(s.1 i).val := by
          simpa [B, q0] using (maternTensor_profileEnergy_le (d := d) (M := M)
            κ h hdecay q hκ hh hdecay_pos Cres hCres hres t M s.1)
        _ = (∏ i : Fin d, B i) * q0^n := hprofileBound s
    _ = (Fintype.card prof : ℝ) * ((∏ i : Fin d, B i) * q0^n) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (((n+1:ℕ):ℝ)^(d-1))) * ((∏ i : Fin d, B i) * q0^n) := by
      apply mul_le_mul_of_nonneg_right hprofiles
      positivity
    _ = _ := by
      dsimp [B, q0]
      ring

/-- Uniform total-grade fiber count for the actual tensor frame, with the
central and signed-frequency ranks already included in the `18q` constant. -/
theorem maternTensorGrade_card_le {d M : ℕ} (hd : 0 < d)
    (κ : Fin d → ℝ) (h r : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hr : 1/2 < r) :
    ∀ n, (Fintype.card {u : ∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M //
        maternTensorGrade κ h r q hκ hh u = n} : ℝ) ≤
      (2 * ∏ i : Fin d, (18*q : ℝ)) * (2:ℝ)^n *
        (((n+1:ℕ):ℝ)^(d-1)) := by
  intro n
  let U := AxisFiltration κ h q hκ hh
  let α : Fin d → ℝ := fun _ => r
  let prof := {s : HaarGradeProfileBox d M //
    weightedProfileGrade α r (profileNat s) = n}
  let fib := {u : ∀ i : Fin d, GradedFrameIndex (U i) M //
    weightedProfileGrade α r (profileNat (fun i => (u i).1)) = n}
  have hsumNat (s : prof) :
      (∑ i : Fin d, (profileNat s.1 i : ℕ)) = n := by
    have hrpos : 0 < r := lt_trans (by norm_num : (0:ℝ)<1/2) hr
    have hfloor : Nat.floor (∑ i : Fin d, (profileNat s.1 i : ℝ)) = n := by
      simpa [prof, weightedProfileGrade, α, profileNat, div_self hrpos.ne'] using s.2
    have hcast : (∑ i : Fin d, (profileNat s.1 i : ℝ)) =
        ((∑ i : Fin d, profileNat s.1 i : ℕ) : ℝ) := by norm_cast
    rw [hcast, Nat.floor_natCast] at hfloor
    exact hfloor
  let Fiber (s : prof) := ∀ i : Fin d, GradeIndex (U i) (s.1 i).val
  let equiv : fib ≃ Σ s : prof, Fiber s := {
    toFun := fun u => ⟨⟨fun i => (u.1 i).1, u.2⟩, fun i => (u.1 i).2⟩
    invFun := fun z => ⟨(fun i => ⟨z.1.1 i, z.2 i⟩), z.1.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      funext i
      exact Sigma.eta (u.1 i)
    right_inv := by
      intro z
      cases z with
      | mk s fiber =>
        apply Sigma.ext (Subtype.ext rfl)
        exact HEq.rfl }
  have hcardNat : Fintype.card fib =
      ∑ s : prof, Fintype.card (Fiber s) := by
    calc
      _ = Fintype.card (Σ s : prof, Fiber s) := Fintype.card_congr equiv
      _ = _ := Fintype.card_sigma
  have hA : ∀ i g, Fintype.card (GradeIndex (U i) g) ≤ (18*q)*2^g := by
    intro i g
    exact axisGrade_card_le d κ h q hκ hh i g
  have hprofile (s : prof) :
      (Fintype.card (Fiber s) : ℝ) ≤
        (∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n := by
    have hpi : Fintype.card (Fiber s) =
        ∏ i : Fin d, Fintype.card (GradeIndex (U i) (s.1 i).val) := by
      simp [Fiber, Fintype.card_pi]
    rw [hpi]
    push_cast
    calc
      (∏ i : Fin d, (Fintype.card (GradeIndex (U i) (s.1 i).val) : ℝ)) ≤
          ∏ i : Fin d, ((18*q:ℝ) * (2:ℝ)^(s.1 i).val) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Nat.cast_nonneg _
        · intro i hi
          exact_mod_cast hA i (s.1 i).val
      _ = (∏ i : Fin d, (18*q:ℝ)) * (2:ℝ) ^
            (∑ i : Fin d, (s.1 i).val) := by
        rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
      _ = _ := by
        have hsumNat' : (∑ i : Fin d, (s.1 i).val) = n := by
          simpa [profileNat] using hsumNat s
        rw [hsumNat']
  have hprofiles := maternProfile_card_le (M := M) hd r hr n
  have hprofiles' : (Fintype.card prof : ℝ) ≤
      2 * (((n+1:ℕ):ℝ)^(d-1)) := by
    simpa [prof, α] using hprofiles
  have hfibBound :
      (∑ s : prof, (Fintype.card (Fiber s) : ℝ)) ≤
        (Fintype.card prof : ℝ) * ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) := by
    calc
      _ ≤ ∑ _s : prof, ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) :=
        Finset.sum_le_sum fun s hs => hprofile s
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hbound : (Fintype.card fib : ℝ) ≤
      (2 * (((n+1:ℕ):ℝ)^(d-1))) *
        ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) := by
    calc
      (Fintype.card fib : ℝ) =
          ∑ s : prof, (Fintype.card (Fiber s) : ℝ) := by exact_mod_cast hcardNat
      _ ≤ (Fintype.card prof : ℝ) *
          ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) := hfibBound
      _ ≤ (2 * (((n+1:ℕ):ℝ)^(d-1))) *
          ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) :=
        mul_le_mul_of_nonneg_right hprofiles' (by positivity)
  have hfibDef :
      (Fintype.card {u : ∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M //
        maternTensorGrade κ h r q hκ hh u = n} : ℝ) =
        (Fintype.card fib : ℝ) := by
    congr 1
  calc
    _ = (Fintype.card fib : ℝ) := hfibDef
    _ ≤ (2 * (((n+1:ℕ):ℝ)^(d-1))) *
        ((∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n) := hbound
    _ = (2 * ∏ i : Fin d, (18*q:ℝ)) * (2:ℝ)^n *
          (((n+1:ℕ):ℝ)^(d-1)) := by ring_nf

def maternTensorContractionEta (hdecay : ℝ) : ℝ :=
  Real.sqrt (Real.rpow 2 (-2*hdecay)/2)

def maternTensorVarianceConstant {d : ℕ} (hdecay : ℝ) (Cres : Fin d → ℝ) : ℝ :=
  (2 * ∏ i : Fin d, (1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2)) *
    (AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
      AlignmentGeometricRanks.polynomialBudget (Real.rpow 2 (-2*hdecay)) (d-1))

/-! The next theorem is the actual uniform-frame variance input to the
Gaussian grid reverse lemma. It contracts the genuine coefficient energy
proved above; the only analytic premise is the scalar projection residual. -/

theorem maternTensor_contracted_variance_le {d M : ℕ} (hd : 0 < d)
    (κ : Fin d → ℝ) (h hdecay r : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (hr : 1/2 < r) (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h x (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h x (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∀ (t : BrownianCubeAnchor d) (N : ℕ),
        (∑ u : (∀ i : Fin d,
          GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
          (contractionScale (maternTensorContractionEta hdecay) N
              (maternTensorGrade κ h r q hκ hh u) *
            ⟪maternSheetFeature κ h hκ hh t,
              tensorGradedFrame κ h q hκ hh u⟫)^2) ≤
          maternTensorVarianceConstant hdecay Cres *
            (Real.rpow 2 (-(2*hdecay) * (N:ℝ) / 2))^2 *
              (((N+1:ℕ):ℝ)^(d-1)) := by
  intro t N
  let q0 : ℝ := Real.rpow 2 (-2*hdecay)
  let η : ℝ := maternTensorContractionEta hdecay
  let B : Fin d → ℝ := fun i =>
    1 + Cres i ^ 2 / (Real.rpow 2 (-hdecay)) ^ 2
  let Cenergy : ℝ := 2 * ∏ i : Fin d, B i
  let Cbudget : ℝ :=
    AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
      AlignmentGeometricRanks.polynomialBudget q0 (d-1)
  let Cvar : ℝ := maternTensorVarianceConstant hdecay Cres
  have hq0 : 0 < q0 := by
    dsimp [q0]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hq01 : q0 < 1 := by
    dsimp [q0]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hη : 0 < η := by
    dsimp [η]
    apply Real.sqrt_pos.2
    positivity
  have hηsq : η^2 = q0/2 := by
    change (Real.sqrt (q0/2))^2 = q0/2
    rw [Real.sq_sqrt (by positivity)]
  have hη1 : η ≤ 1 := by
    have hq02 : q0/2 < 1 := by linarith
    have hsqrt : Real.sqrt (q0/2) < 1 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ q0/2 by positivity)]
    dsimp [η]
    exact hsqrt.le
  have hB : ∀ i, 0 ≤ B i := by
    intro i
    dsimp [B]
    positivity
  have hCenergy : 0 ≤ Cenergy := by
    dsimp [Cenergy]
    positivity
  have hCbudget : 0 ≤ Cbudget := by
    dsimp [Cbudget]
    exact add_nonneg
      (AlignmentGeometricRanks.polynomialBudget_nonneg (by norm_num) 0)
      (AlignmentGeometricRanks.polynomialBudget_nonneg hq0.le (d-1))
  have hCvar : 0 ≤ Cvar := by
    dsimp [Cvar, maternTensorVarianceConstant]
    exact mul_nonneg hCenergy hCbudget
  have hCvar_eq : Cvar = Cenergy * Cbudget := by
    dsimp [Cvar, maternTensorVarianceConstant, Cenergy, Cbudget, B, q0]
  have hbase : q0 = (Real.rpow 2 (-hdecay))^2 := by
    dsimp [q0]
    calc
      Real.rpow 2 (-2*hdecay) = Real.rpow 2 ((-hdecay)*2) := by
        congr 1 <;> ring
      _ = Real.rpow (Real.rpow 2 (-hdecay)) (2:ℝ) :=
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-hdecay) 2
      _ = _ := Real.rpow_natCast _ _
  let grade : (∀ i : Fin d,
      GradedFrameIndex (AxisFiltration κ h q hκ hh i) M) → ℕ :=
    maternTensorGrade κ h r q hκ hh
  let coeff : (∀ i : Fin d,
      GradedFrameIndex (AxisFiltration κ h q hκ hh i) M) → ℝ := fun u =>
    ⟪maternSheetFeature κ h hκ hh t, tensorGradedFrame κ h q hκ hh u⟫
  have henergy : ∀ g : ℕ,
      (∑ u : {u : ∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M // grade u = g},
        (coeff u.1)^2) ≤ Cenergy * ((g+1:ℕ):ℝ)^(d-1) * q0^g := by
    intro g
    have htEnergy := maternTensor_totalGradeEnergy_le (M := M) hd κ h hdecay r q
      hκ hh hdecay_pos hr Cres hCres hres t g
    change (∑ u : {u : ∀ i : Fin d,
        GradedFrameIndex (AxisFiltration κ h q hκ hh i) M //
        maternTensorGrade κ h r q hκ hh u = g},
        ⟪maternSheetFeature κ h hκ hh t,
          tensorGradedFrame κ h q hκ hh u.1⟫^2) ≤ _ at htEnergy
    have hpow : q0^g = ((Real.rpow 2 (-hdecay))^2)^g := by rw [hbase]
    simpa [Cenergy, B, grade, coeff, hpow, mul_assoc, mul_left_comm,
      mul_comm] using htEnergy
  have hcontract := graded_contracted_square_sum_le_uniform
    (grade := grade) coeff hq0 hq01 hηsq hCenergy (d-1) N henergy
  change (∑ u : (∀ i : Fin d,
      GradedFrameIndex (AxisFiltration κ h q hκ hh i) M),
      (contractionScale η N (maternTensorGrade κ h r q hκ hh u) *
        ⟪maternSheetFeature κ h hκ hh t,
          tensorGradedFrame κ h q hκ hh u⟫)^2) ≤ _
  have hrate :
      (Real.rpow 2 (-(2*hdecay) * (N:ℝ) / 2))^2 = q0^N := by
    have hgeneral (β : ℝ) :
        (Real.rpow 2 (-β * (N:ℝ) / 2))^2 = (Real.rpow 2 (-β))^N := by
      calc
        (Real.rpow 2 (-β * (N:ℝ) / 2))^2 =
            Real.rpow 2 ((-β * (N:ℝ) / 2) * 2) := by
              calc
                _ = Real.rpow (Real.rpow 2 (-β * (N:ℝ) / 2)) (2:ℝ) :=
                  (Real.rpow_natCast _ _).symm
                _ = _ := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)
                  (-β*(N:ℝ)/2) 2).symm
        _ = Real.rpow 2 (-β * (N:ℝ)) := by congr 1 <;> ring
        _ = (Real.rpow 2 (-β))^N := by
          calc
            _ = Real.rpow (Real.rpow 2 (-β)) (N:ℝ) :=
              Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-β) (N:ℝ)
            _ = _ := Real.rpow_natCast _ _
    simpa [q0] using hgeneral (2*hdecay)
  calc
    _ ≤ Cenergy * q0^N * (((N+1:ℕ):ℝ)^(d-1)) *
        (AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
          AlignmentGeometricRanks.polynomialBudget q0 (d-1)) := by
      simpa [grade, coeff, q0] using hcontract
    _ = Cvar * (Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2))^2 *
        (((N+1:ℕ):ℝ)^(d-1)) := by
      calc
        _ = (Cenergy * Cbudget) * q0^N * (((N+1:ℕ):ℝ)^(d-1)) := by ring
        _ = Cvar * q0^N * (((N+1:ℕ):ℝ)^(d-1)) := by rw [← hCvar_eq]
        _ = _ := by rw [hrate]

/-- The actual tensor-frame projection converges uniformly whenever the
coordinate cumulative projections do. This is the finite-frame approximation
input consumed by the Gaussian grid reverse theorem. -/
theorem maternTensorFrame_projection_error_le {d M : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (q : ℕ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (δ : Fin d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hres : ∀ i (t : BrownianCubeAnchor d),
      ‖normalizedAxis (κ i) h (t.val i) (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q M (hκ i) hh).starProjection
          (normalizedAxis (κ i) h (t.val i) (hκ i) hh)‖ ≤ δ i)
    (t : BrownianCubeAnchor d) :
    ‖maternSheetFeature κ h hκ hh t -
      GaussianProjection.projection (tensorGradedFrame κ h q hκ hh (M := M))
        (maternSheetFeature κ h hκ hh t)‖ ≤ (d:ℝ) * ∑ i, δ i := by
  classical
  let μ : Fin d → Measure ℝ := fun i => spectralMeasure (κ i) h
  letI (i : Fin d) : IsFiniteMeasure (μ i) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  let T := AlignmentSigmaFiniteL2Tensor.tensorContinuous (μ := μ)
  let U := AxisFiltration κ h q hκ hh
  let fin : ∀ i n, FiniteDimensional ℝ ↥(U i n) := fun i n =>
    cumulativeLevelSpace_finiteDimensional (κ i) h q n (hκ i) hh
  let nest : ∀ i n, U i n ≤ U i (n+1) := fun i n =>
    cumulativeLevelSpace_nested (κ i) h q n (hκ i) hh
  let v : (i : Fin d) → SpectralAxisL2 (κ i) h := fun i =>
    normalizedAxis (κ i) h (t.val i) (hκ i) hh
  let w : (i : Fin d) → SpectralAxisL2 (κ i) h := fun i => (U i M).starProjection (v i)
  have hv (i : Fin d) : ‖v i‖ = 1 := normalizedAxis_norm (κ i) h (t.val i) (hκ i) hh
  have hproj (i : Fin d) : ‖(U i M).starProjection‖ ≤ 1 :=
    (U i M).starProjection_norm_le
  have hw (i : Fin d) : ‖w i‖ ≤ 1 := by
    calc
      ‖w i‖ ≤ ‖(U i M).starProjection‖ * ‖v i‖ :=
        (U i M).starProjection.le_opNorm (v i)
      _ ≤ 1 := by rw [hv i]; simpa using hproj i
  have hnormv : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
    intro i
    rw [hv i]
  have hnormw : ‖w‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
    intro i
    exact hw i
  have hdiff : ‖v-w‖ ≤ ∑ i : Fin d, δ i := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i hi => hδ i)).2
    intro i
    exact (hres i t).trans (Finset.single_le_sum
      (f := δ) (s := Finset.univ) (fun j hj => hδ j) (Finset.mem_univ i))
  have hTnorm : ‖T‖ ≤ 1 := by
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
        have hmax : max ‖v‖ ‖w‖ ≤ 1 := max_le hnormv hnormw
        have hsum : 0 ≤ ∑ i : Fin d, δ i := Finset.sum_nonneg fun i hi => hδ i
        have hpow : max ‖v‖ ‖w‖ ^ (d-1) ≤ 1 := by
          calc
            _ ≤ (1:ℝ)^(d-1) := pow_le_pow_left₀ (by positivity) hmax _
            _ = 1 := one_pow _
        have hfactor1 : ‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) ≤
            1 * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) := by gcongr
        have hfactor2 : 1 * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) ≤
            1 * (d:ℝ) * 1^(d-1) := by gcongr
        have hfactor := hfactor1.trans hfactor2
        calc
          _ = (‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1)) * ‖v-w‖ := rfl
          _ ≤ (1 * (d:ℝ) * 1^(d-1)) * ‖v-w‖ :=
            mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
          _ ≤ (1 * (d:ℝ) * 1^(d-1)) * (∑ i : Fin d, δ i) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (d:ℝ) * ∑ i : Fin d, δ i := by simp
  have hactual : maternSheetFeature κ h hκ hh t = T v := by
    simp [maternSheetFeature, T, v, AlignmentSigmaFiniteL2Tensor.tensorContinuous_apply]
  have hcoord (i : Fin d) : w i =
      ∑ a : GradedFrameIndex (U i) M,
        ⟪v i, gradedFrame (U i) (fin i) M a⟫ • gradedFrame (U i) (fin i) M a := by
    let e := gradedFrame (U i) (fin i) M
    let W : Submodule ℝ (SpectralAxisL2 (κ i) h) := Submodule.span ℝ (Set.range e)
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
    letI : CompleteSpace W := FiniteDimensional.complete ℝ W
    let p := BrownianSharp.finiteOrthonormalProjection e (v i)
    have hspan : W = U i M := gradedFrame_span_eq (U i) (fin i) (nest i) M
    have horth : Orthonormal ℝ e := gradedFrame_orthonormal (U i) (fin i) (nest i) M
    have hmem : p ∈ U i M := by
      rw [← hspan]
      dsimp [p, BrownianSharp.finiteOrthonormalProjection, W]
      apply Submodule.sum_mem
      intro a ha
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)
    have hresid : v i-p ∈ (U i M)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      rw [← hspan] at hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · rintro y ⟨a,rfl⟩
        exact BrownianSharp.finiteProjection_residual_orthogonal e (v i)
          (orthonormal_iff_ite.mp horth) a
      · simp
      · intro y z hy hz hpy hpz
        rw [inner_add_right, hpy, hpz]
        simp
      · intro c y hy hpy
        rw [inner_smul_right, hpy]
        simp
    have hp := (U i M).eq_starProjection_of_mem_orthogonal hmem hresid
    simpa [w, p, e, BrownianSharp.finiteOrthonormalProjection] using hp
  have hcandidate : T w ∈
      Submodule.span ℝ (Set.range (tensorGradedFrame κ h q hκ hh (M := M))) := by
    have hexpand : T w =
        ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) M),
          (∏ i, ⟪v i, gradedFrame (U i) (fin i) M (a i)⟫) •
            tensorGradedFrame κ h q hκ hh a := by
      calc
        _ = T (fun i => ∑ a : GradedFrameIndex (U i) M,
            ⟪v i, gradedFrame (U i) (fin i) M a⟫ • gradedFrame (U i) (fin i) M a) := by
              congr 1
              funext i
              exact hcoord i
        _ = ∑ a : (∀ i : Fin d, GradedFrameIndex (U i) M),
            T (fun i => ⟪v i, gradedFrame (U i) (fin i) M (a i)⟫ •
              gradedFrame (U i) (fin i) M (a i)) :=
            T.map_sum (fun i a => ⟪v i, gradedFrame (U i) (fin i) M a⟫ •
              gradedFrame (U i) (fin i) M a)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [T.map_smul_univ]
          simp [tensorGradedFrame, AxisFiltration, axisFiltration, U, fin, T,
            AlignmentSigmaFiniteL2Tensor.tensorContinuous_apply]
    rw [hexpand]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  let e := tensorGradedFrame κ h q hκ hh (M := M)
  let W : Submodule ℝ (SpectralProductL2 κ h) := Submodule.span ℝ (Set.range e)
  let p := BrownianSharp.finiteOrthonormalProjection e (T v)
  have horth : Orthonormal ℝ e := tensorGradedFrame_orthonormal κ h q hκ hh
  have hp_mem : p ∈ W := by
    dsimp [p, BrownianSharp.finiteOrthonormalProjection, W]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)
  have hp_orth : T v-p ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    dsimp [W] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro y ⟨a,rfl⟩
      exact BrownianSharp.finiteProjection_residual_orthogonal e (T v)
        (orthonormal_iff_ite.mp horth) a
    · simp
    · intro y z hy hz hpy hpz
      rw [inner_add_right, hpy, hpz]
      simp
    · intro c y hy hpy
      rw [inner_smul_right, hpy]
      simp
  have hcross : ⟪T v-p, p-T w⟫ = 0 := by
    rw [Submodule.mem_orthogonal'] at hp_orth
    exact hp_orth (p-T w) (Submodule.sub_mem _ hp_mem hcandidate)
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (T v-p) (p-T w) hcross
  have hdecomp : T v-T w = (T v-p)+(p-T w) := by abel
  have hmin : ‖T v-p‖ ≤ ‖T v-T w‖ := by
    have hsq : ‖T v-p‖^2 ≤ ‖T v-T w‖^2 := by
      calc
        ‖T v-p‖^2 ≤ ‖T v-p‖^2 + ‖p-T w‖^2 := by
          nlinarith [sq_nonneg ‖p-T w‖]
        _ = ‖(T v-p)+(p-T w)‖^2 := by simpa [pow_two] using hpyth.symm
        _ = ‖T v-T w‖^2 := by rw [← hdecomp]
    have hnp : 0 ≤ ‖T v-p‖ := norm_nonneg _
    have hnq : 0 ≤ ‖T v-T w‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T v-p‖ - ‖T v-T w‖)]
  have hproj : p = GaussianProjection.projection e (T v) := by
    simp [p, BrownianSharp.finiteOrthonormalProjection,
      GaussianProjection.projection, e]
    apply Finset.sum_congr rfl
    intro a ha
    rw [real_inner_comm]
  rw [hactual, ← hproj]
  calc
    ‖T v-p‖ ≤ ‖T v-T w‖ := hmin
    _ ≤ (d:ℝ) * ∑ i, δ i := hmult'

/-- Uniform scalar geometric projection convergence supplies a finite starting
depth after which every coordinate grade frame is nonempty. This avoids an
unneeded standalone lower-rank estimate for the central cell generators. -/
theorem maternTensor_frame_nonempty_after_depth {d : ℕ} (hd : 0 < d)
    (κ : Fin d → ℝ) (h hdecay : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h x (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h x (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∃ M0, ∀ M i,
      Nonempty (GradedFrameIndex (AxisFiltration κ h q hκ hh i) (M+M0)) := by
  classical
  let decay : ℝ := Real.rpow 2 (-hdecay)
  let qgeo : Fin d → ℝ := fun _ => decay^2
  let err : Fin d → ℕ → Unit → ℝ := fun i N _ => Cres i * decay^N
  let Cbound : Fin d → ℝ := fun i => Cres i^2
  have hq0 : ∀ i, 0 ≤ qgeo i := by intro i; positivity
  have hq1 : ∀ i, qgeo i < 1 := by
    intro i
    have hdec0 : 0 < decay := by
      dsimp [decay]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hdec1 : decay < 1 := by
      dsimp [decay]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    dsimp [qgeo]
    have hm : 0 < (1-decay)*(1+decay) :=
      mul_pos (sub_pos.mpr hdec1) (by linarith)
    nlinarith [hm]
  have herr0 : ∀ i N u, 0 ≤ err i N u := by
    intro i N u
    dsimp [err]
    exact mul_nonneg (hCres i) (pow_nonneg (by
      dsimp [decay]
      exact (Real.rpow_pos_of_pos (by norm_num) _).le) _)
  have hpow (N : ℕ) : (decay^N)^2 = (decay^2)^N := by
    rw [pow_two, pow_two, ← mul_pow]
  have herr : ∀ i N u, (err i N u)^2 ≤ Cbound i * (qgeo i)^N := by
    intro i N u
    change (Cres i * decay^N)^2 ≤ Cres i^2 * (decay^2)^N
    rw [mul_pow, hpow]
  obtain ⟨M0, hsmall⟩ :=
    AlignmentUniformGeometricApproximation.uniform_small_of_squared_geometric
      err Cbound qgeo hq0 hq1 herr0 herr (δ := (1/2:ℝ)) (by norm_num)
  refine ⟨M0, fun M i => ?_⟩
  let n := M + M0
  let U := AxisFiltration κ h q hκ hh i n
  let x := normalizedAxis (κ i) h 0 (hκ i) hh
  letI : U.HasOrthogonalProjection :=
    cumulativeLevelSpace_hasOrthogonalProjection (κ i) h q n (hκ i) hh
  letI : FiniteDimensional ℝ ↥U :=
    cumulativeLevelSpace_finiteDimensional (κ i) h q n (hκ i) hh
  let p := U.starProjection x
  have hresid : ‖x-p‖ ≤ 1/2 := by
    have hraw := hres i 0 (by norm_num) (by norm_num) n
    have hn : M0 ≤ n := by dsimp [n]; omega
    have hdec0 : 0 ≤ decay := by
      dsimp [decay]
      exact (Real.rpow_pos_of_pos (by norm_num) _).le
    have hdec1 : decay ≤ 1 := (le_of_lt (by
      dsimp [decay]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
    have hpowle : decay^n ≤ decay^M0 := pow_le_pow_of_le_one hdec0 hdec1 hn
    have htail : Cres i * decay^n ≤ Cres i * decay^M0 := by
      have hdiff := mul_nonneg (hCres i) (sub_nonneg.mpr hpowle)
      nlinarith
    have hs := hsmall i ()
    change Cres i * decay^M0 ≤ 1/2 at hs
    change ‖x-p‖ ≤ 1/2
    exact (hraw.trans (htail.trans hs))
  have hpnorm : p ≠ 0 := by
    intro hp
    have hxnorm : ‖x‖ = 1 := normalizedAxis_norm (κ i) h 0 (hκ i) hh
    rw [hp, sub_zero, hxnorm] at hresid
    norm_num at hresid
  have hnonzero : ∃ z : U, z ≠ 0 := by
    refine ⟨⟨p, U.starProjection_apply_mem x⟩, ?_⟩
    intro hz
    apply hpnorm
    exact congrArg Subtype.val hz
  have hdim : 0 < Module.finrank ℝ ↥U :=
    (Module.finrank_pos_iff_exists_ne_zero).2 hnonzero
  have hcard : 0 < Fintype.card (GradedFrameIndex (AxisFiltration κ h q hκ hh i) n) := by
    rw [gradedFrameIndex_card_eq_finrank
      (AxisFiltration κ h q hκ hh i)
      (fun k => cumulativeLevelSpace_finiteDimensional (κ i) h q k (hκ i) hh)
      (fun k => cumulativeLevelSpace_nested (κ i) h q k (hκ i) hh) n]
    exact hdim
  exact Fintype.card_pos_iff.mp hcard

/-- The actual Matérn tensor frame satisfies every hypothesis of the uniform
Gaussian grid reverse theorem. This theorem is the consumer-facing bridge from
the scalar projection residual to the small-ball upper-log endpoint. -/
theorem maternTensor_grid_lower_bound_of_scalar_residual {d : ℕ} (hd : 0 < d)
    (κ : Fin d → ℝ) (h hdecay : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h x (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h x (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [Nonempty J]
        {P : Measure Ω} [IsProbabilityMeasure P]
        (X : Ω → J → ℝ) (x : J → BrownianCubeAnchor d),
        HasGaussianLaw (fun ω j => X ω j) P →
        (∀ j, ∫ ω, X ω j ∂P = 0) →
        (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
          ⟪maternSheetFeature κ h hκ hh (x i),
            maternSheetFeature κ h hκ hh (x j)⟫) →
        ∀ N, ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N *
          (((N+1:ℕ):ℝ)^(d-1)))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |X ω j| ≤
            2*A*Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
              Real.sqrt (((N+1:ℕ):ℝ)^d)} := by
  classical
  obtain ⟨M0, hnonemptyAxis⟩ := maternTensor_frame_nonempty_after_depth
    hd κ h hdecay q hκ hh hdecay_pos Cres hCres hres
  obtain ⟨Rvar, hRvar, hHolder⟩ :=
    maternSheetFeature_increment_holder κ h hκ hh
  let θ := maternHolderExponent h
  let β := 2*hdecay
  let η := maternTensorContractionEta hdecay
  let Cvar := maternTensorVarianceConstant hdecay Cres
  let Cdim := 2 * ∏ i : Fin d, (18*q:ℝ)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hθ : 0 < θ := by dsimp [θ]; exact maternHolderExponent_pos hh
  have hθ1 : θ ≤ 1 := by
    dsimp [θ, maternHolderExponent]
    have := min_le_right (h/2) (1/2:ℝ)
    linarith
  have hη : 0 < η := by
    dsimp [η, maternTensorContractionEta]
    apply Real.sqrt_pos.2
    positivity
  have hη1 : η ≤ 1 := by
    have hq0 : Real.rpow 2 (-2*hdecay) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hq02 : Real.rpow 2 (-2*hdecay)/2 < 1 := by linarith
    have hqarg : 0 ≤ Real.rpow 2 (-2*hdecay)/2 := by
      exact div_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le (by norm_num)
    have hsq : (Real.sqrt (Real.rpow 2 (-2*hdecay)/2))^2 =
        Real.rpow 2 (-2*hdecay)/2 := Real.sq_sqrt hqarg
    have hsqrt : Real.sqrt (Real.rpow 2 (-2*hdecay)/2) < 1 := by
      nlinarith
    exact hsqrt.le
  have hCvar : 0 ≤ Cvar := by
    dsimp [Cvar, maternTensorVarianceConstant]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (AlignmentGeometricRanks.polynomialBudget_nonneg (by norm_num) 0)
        (AlignmentGeometricRanks.polynomialBudget_nonneg
          (Real.rpow_pos_of_pos (by norm_num) _).le (d-1)))
  have hCdim : 0 ≤ Cdim := by dsimp [Cdim]; positivity
  have hgrid := gradedKernel_grid_lower_bound_of_uniform_frames (d := d)
    β θ Cvar Rvar Cdim η (d-1) hβ hθ hCvar hRvar.le hCdim hη hη1
  obtain ⟨A,D,hA,hD,hgeneric⟩ := hgrid
  refine ⟨A,D,hA,hD,?_⟩
  intro Ω J _ _ _ P _ X x hLaw hMean hCov
  let F : ℕ → Type := fun M => ∀ i : Fin d,
    GradedFrameIndex (AxisFiltration κ h q hκ hh i) (M+M0)
  let e : ∀ M, F M → SpectralProductL2 κ h := fun M u =>
    tensorGradedFrame κ h q hκ hh u
  let gr : ∀ M, F M → ℕ := fun M u => maternTensorGrade κ h 1 q hκ hh u
  let hfinite : ∀ M, Fintype (F M) := by intro M; dsimp [F]; infer_instance
  let hdecEq : ∀ M, DecidableEq (F M) := by intro M; dsimp [F]; infer_instance
  have hne : ∀ M, Nonempty (F M) := by
    intro M
    exact ⟨fun i => Classical.choice (hnonemptyAxis M i)⟩
  have horth : ∀ M, letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ u v, ⟪e M u, e M v⟫ = if u = v then 1 else 0 := by
    intro M
    letI : Fintype (F M) := hfinite M
    letI : DecidableEq (F M) := hdecEq M
    intro u v
    exact orthonormal_iff_ite.mp
      (tensorGradedFrame_orthonormal κ h q hκ hh (M := M+M0)) u v
  have hvar : ∀ M N, letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ∑ u : F M,
        (contractionScale η N (gr M u) * ⟪maternSheetFeature κ h hκ hh z,
          e M u⟫)^2 ≤
        Cvar * (Real.rpow 2 (-β*(N:ℝ)/2))^2 * (((N+1:ℕ):ℝ)^(d-1)) := by
    intro M N
    letI : Fintype (F M) := hfinite M
    letI : DecidableEq (F M) := hdecEq M
    intro z
    simpa [F, e, gr, β, η, Cvar, hfinite] using
      (maternTensor_contracted_variance_le (M := M+M0) hd κ h hdecay 1 q
        hκ hh hdecay_pos (by norm_num) Cres hCres hres z N)
  have hincrement : ∀ M N, letI : Fintype (F M) := hfinite M
      ∀ z w, ∑ u : F M,
        (contractionScale η N (gr M u) *
          (⟪maternSheetFeature κ h hκ hh z, e M u⟫ -
            ⟪maternSheetFeature κ h hκ hh w, e M u⟫))^2 ≤
        Rvar * (dist z w)^(2*θ) := by
    intro M N
    letI : Fintype (F M) := hfinite M
    intro z w
    have hbase := tensorFrame_increment_le_holder (M := M+M0)
      κ h q hκ hh z w
    calc
      _ ≤ ∑ u : F M,
          (⟪maternSheetFeature κ h hκ hh z,e M u⟫ -
            ⟪maternSheetFeature κ h hκ hh w,e M u⟫)^2 := by
        apply Finset.sum_le_sum
        intro u hu
        let s := contractionScale η N (gr M u)
        have hs : 0 ≤ s ∧ s ≤ 1 := by
          dsimp [s]
          exact ⟨(contractionScale_pos hη N _).le,
            contractionScale_le_one hη.le hη1 N _⟩
        have hsq : s^2 ≤ 1 := by nlinarith
        have hfactor : 0 ≤ 1-s^2 := by linarith
        have hsqdiff : 0 ≤
            (⟪maternSheetFeature κ h hκ hh z,e M u⟫ -
              ⟪maternSheetFeature κ h hκ hh w,e M u⟫)^2 := sq_nonneg _
        nlinarith [mul_nonneg hfactor hsqdiff]
      _ ≤ ‖maternSheetFeature κ h hκ hh z -
          maternSheetFeature κ h hκ hh w‖^2 := by
        simpa [F, e, hfinite] using hbase
      _ ≤ Rvar * (dist z w)^(2*θ) := by
        simpa [θ] using hHolder z w
  have hfiber : ∀ M N, letI : Fintype (F M) := hfinite M
      ∀ g : Fin (N+1),
        (Fintype.card {u : F M // gr M u = g.val} : ℝ) ≤
          Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^(d-1)) := by
    intro M N g
    letI : Fintype (F M) := hfinite M
    simpa [F, gr, Cdim, hfinite] using
      (maternTensorGrade_card_le hd κ h 1 q hκ hh (by norm_num : (1/2:ℝ) < 1) g.val)
  have happrox : ∀ ε, 0 < ε → ∃ M,
      letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ‖maternSheetFeature κ h hκ hh z -
        GaussianProjection.projection (e M) (maternSheetFeature κ h hκ hh z)‖ ≤ ε := by
    intro ε hε
    let δ : ℝ := ε / ((d:ℝ)^2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let decay : ℝ := Real.rpow 2 (-hdecay)
    let qgeo : Fin d → ℝ := fun _ => decay^2
    let err : Fin d → ℕ → Unit → ℝ := fun i n _ => Cres i * decay^n
    let Cbound : Fin d → ℝ := fun i => Cres i^2
    have hq0 : ∀ i, 0 ≤ qgeo i := by intro i; positivity
    have hq1 : ∀ i, qgeo i < 1 := by
      intro i
      have hd0 : 0 < decay := by dsimp [decay]; positivity
      have hd1 : decay < 1 := by
        dsimp [decay]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      dsimp [qgeo]
      have hm : 0 < (1-decay)*(1+decay) :=
        mul_pos (sub_pos.mpr hd1) (by linarith)
      nlinarith [hm]
    have herr0 : ∀ i n u, 0 ≤ err i n u := by
      intro i n u
      dsimp [err]
      exact mul_nonneg (hCres i) (pow_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le n)
    have hpow (n : ℕ) : (decay^n)^2 = (decay^2)^n := by
      rw [pow_two, pow_two, ← mul_pow]
    have herr : ∀ i n u, (err i n u)^2 ≤ Cbound i * (qgeo i)^n := by
      intro i n u
      change (Cres i * decay^n)^2 ≤ Cres i^2 * (decay^2)^n
      rw [mul_pow, hpow]
    obtain ⟨m, hm⟩ :=
      AlignmentUniformGeometricApproximation.uniform_small_of_squared_geometric
        err Cbound qgeo hq0 hq1 herr0 herr hδ
    refine ⟨m,?_⟩
    letI : Fintype (F m) := hfinite m
    letI : DecidableEq (F m) := hdecEq m
    intro z
    let n := m+M0
    have hcoord : ∀ i (t : BrownianCubeAnchor d),
        ‖normalizedAxis (κ i) h (t.val i) (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q n (hκ i) hh).starProjection
          (normalizedAxis (κ i) h (t.val i) (hκ i) hh)‖ ≤ δ := by
      intro i t
      have ht : 0 ≤ t.val i ∧ t.val i ≤ 1 := Set.mem_Icc.mp (t.property i)
      have hraw := hres i (t.val i) ht.1 ht.2 n
      have hn : m ≤ n := by dsimp [n]; omega
      have hd0 : 0 ≤ decay := by dsimp [decay]; positivity
      have hd1 : decay ≤ 1 := by
        dsimp [decay]
        exact (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
      have hpowle : decay^n ≤ decay^m := pow_le_pow_of_le_one hd0 hd1 hn
      have htail : Cres i * decay^n ≤ Cres i * decay^m := by
        have hdiff := mul_nonneg (hCres i) (sub_nonneg.mpr hpowle)
        nlinarith
      have hsmall := hm i ()
      change Cres i * decay^m ≤ δ at hsmall
      have hdecay_eq : Real.rpow 2 (-hdecay) = decay := rfl
      simpa [hdecay_eq] using hraw.trans (htail.trans hsmall)
    have hproj := maternTensorFrame_projection_error_le
      (κ := κ) (h := h) (q := q) (M := n) hκ hh
      (fun _ => δ) (fun _ => le_of_lt hδ) (by intro i t; exact hcoord i t) z
    have hsum : (∑ i : Fin d, δ) = (d:ℝ)*δ := by
      simp [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (d:ℝ) * ∑ i : Fin d, δ := hproj
      _ = ε := by
        have hdne : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
        rw [hsum]
        dsimp [δ]
        ring_nf
        field_simp [hdne]
  have hfinal := hgeneric F hfinite hdecEq hne (X := X)
    (K := maternSheetFeature κ h hκ hh) (x := x) (e := e) (grade := gr)
    horth hvar hincrement hfiber happrox hLaw hMean hCov
  simpa [β, Nat.sub_add_cancel (by omega : 1 ≤ d)] using hfinal

/-- Raw Matérn amplitudes are handled by rescaling the actual Gaussian grid by
the square root of its diagonal variance. The only analytic input remains the
scalar Taylor residual; the covariance passed by callers is exactly the raw
spectral covariance used in `AlignmentPaperMaternFinal`. -/
theorem rawMatern_grid_lower_bound_of_projection_residual {d : ℕ}
    (hd : 0 < d) (κ c : Fin d → ℝ) (h hdecay : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i)
    (hh : 0 < h) (hdecay_pos : 0 < hdecay)
    (Cres : Fin d → ℝ) (hCres : ∀ i, 0 ≤ Cres i)
    (hres : ∀ i (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h t (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h t (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-hdecay)) ^ N) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [Nonempty J]
        {P : Measure Ω} [IsProbabilityMeasure P]
        (X : Ω → J → ℝ) (x : J → BrownianCubeAnchor d),
        HasGaussianLaw (fun ω j => X ω j) P →
        (∀ j, ∫ ω, X ω j ∂P = 0) →
        (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
          BrownianSharp.AlignmentPaperMaternFinal.rawMaternCovariance κ c h
            (x i) (x j)) →
        ∀ N, ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N *
          (((N+1:ℕ):ℝ)^(d-1)))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |X ω j| ≤
            2*A*
              Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
              Real.sqrt (((N+1:ℕ):ℝ)^d)} := by
  let Pscale : ℝ := ∏ i, c i * spectralMass (κ i) h
  let σ : ℝ := Real.sqrt Pscale
  have hPscale : 0 < Pscale := by
    dsimp [Pscale]
    exact Finset.prod_pos fun i hi =>
      mul_pos (hc i) (spectralMass_pos (κ i) h (hκ i) hh)
  have hσ : 0 < σ := by dsimp [σ]; exact Real.sqrt_pos.2 hPscale
  have hσsq : σ^2 = Pscale := by
    dsimp [σ]
    exact Real.sq_sqrt hPscale.le
  obtain ⟨A, D, hA, hD, hgrid⟩ :=
    maternTensor_grid_lower_bound_of_scalar_residual hd κ h hdecay q
      hκ hh hdecay_pos Cres hCres hres
  refine ⟨σ*A, D, mul_pos hσ hA, hD, ?_⟩
  intro Ω J _ _ _ Pmeasure _ X x hLaw hMean hCov
  let Y : Ω → J → ℝ := fun ω j => X ω j / σ
  have hYeq : (fun ω j => Y ω j) = fun ω => σ⁻¹ • (fun j => X ω j) := by
    funext ω j
    simp [Y, div_eq_mul_inv, smul_eq_mul]
    ring
  have hYlaw : HasGaussianLaw (fun ω j => Y ω j) Pmeasure := by
    rw [hYeq]
    exact hLaw.fun_smul (σ⁻¹)
  have hYmean : ∀ j, ∫ ω, Y ω j ∂Pmeasure = 0 := by
    intro j
    rw [show (fun ω => Y ω j) = fun ω => σ⁻¹ * X ω j by
      funext ω; simp [Y, div_eq_mul_inv]; ring]
    rw [integral_const_mul, hMean j]
    ring
  have hrawnorm (s t : BrownianCubeAnchor d) :
      BrownianSharp.AlignmentPaperMaternFinal.rawMaternCovariance κ c h s t =
        Pscale * ⟪maternSheetFeature κ h hκ hh s,
          maternSheetFeature κ h hκ hh t⟫ := by
    rw [maternSheetFeature_gram]
    dsimp [BrownianSharp.AlignmentPaperMaternFinal.rawMaternCovariance,
      Pscale, maternSheetCovariance]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    calc
      c i * stationaryCovariance (κ i) h (s.val i) (t.val i) =
          (c i * spectralMass (κ i) h) *
            normalizedCovariance (κ i) h (s.val i) (t.val i) (hκ i) hh := by
        rw [← BrownianSharp.AlignmentPaperMatern.spectralMass_mul_normalizedCovariance
          (κ i) h (s.val i) (t.val i) (hκ i) hh]
        ring
      _ = _ := by ring
  have hYcov : ∀ i j,
      covariance (fun ω => Y ω i) (fun ω => Y ω j) Pmeasure =
        ⟪maternSheetFeature κ h hκ hh (x i),
          maternSheetFeature κ h hκ hh (x j)⟫ := by
    intro i j
    have hscale : covariance (fun ω => Y ω i) (fun ω => Y ω j) Pmeasure =
        (σ⁻¹)^2 * covariance (fun ω => X ω i) (fun ω => X ω j) Pmeasure := by
      rw [show (fun ω => Y ω i) = fun ω => σ⁻¹ * X ω i by
        funext ω; simp [Y, div_eq_mul_inv]; ring]
      rw [show (fun ω => Y ω j) = fun ω => σ⁻¹ * X ω j by
        funext ω; simp [Y, div_eq_mul_inv]; ring]
      rw [covariance_const_mul_left, covariance_const_mul_right]
      ring
    rw [hscale, hCov i j, hrawnorm]
    rw [← hσsq]
    field_simp [ne_of_gt hσ]
  have hnorm := hgrid Y x hYlaw hYmean hYcov
  intro N
  have hset :
      {ω | ∀ j, |Y ω j| ≤
        2*A*Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
          Real.sqrt (((N+1:ℕ):ℝ)^d)} =
      {ω | ∀ j, |X ω j| ≤
        σ * (2*A*Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
          Real.sqrt (((N+1:ℕ):ℝ)^d))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Y]
    apply forall_congr'
    intro j
    rw [abs_div, abs_of_pos hσ]
    simpa [mul_comm] using (div_le_iff₀ hσ)
  have hrad :
      σ * (2*A*Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
        Real.sqrt (((N+1:ℕ):ℝ)^d)) =
      2*(σ*A)*Real.rpow 2 (-(2*hdecay)*(N:ℝ)/2) *
        Real.sqrt (((N+1:ℕ):ℝ)^d) := by ring
  have hnorm' := hnorm N
  rw [hset, hrad] at hnorm'
  exact hnorm'

/-- The actual uniform coefficient in the scalar level-Taylor residual. -/
def maternScalarTaylorResidualConstant (κ h : ℝ) (q : ℕ) : ℝ :=
  ((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      (spectralMeasure κ h).real Set.univ) +
    ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
      (spectralMeasure κ h).real Set.univ) +
    ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
      (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) + (8/(2*h))

/-- A complete raw-covariance grid reverse endpoint for every positive
Matérn order and positive coordinate amplitudes. The scalar Taylor residual is
proved internally from the actual spectral measure; the polynomial degree is
chosen above `2h`, and level zero is handled by projection minimality against
the zero vector. -/
theorem rawMatern_grid_lower_bound {d : ℕ} (hd : 0 < d)
    (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [Nonempty J]
        {P : Measure Ω} [IsProbabilityMeasure P]
        (X : Ω → J → ℝ) (x : J → BrownianCubeAnchor d),
        HasGaussianLaw (fun ω j => X ω j) P →
        (∀ j, ∫ ω, X ω j ∂P = 0) →
        (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
          BrownianSharp.AlignmentPaperMaternFinal.rawMaternCovariance κ c h
            (x i) (x j)) →
        ∀ N, ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N *
          (((N+1:ℕ):ℝ)^(d-1)))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |X ω j| ≤
            2*A*Real.rpow 2 (-(2*h)*(N:ℝ)/2) *
              Real.sqrt (((N+1:ℕ):ℝ)^d)} := by
  obtain ⟨q, hq⟩ := exists_nat_gt (2*h)
  let C0 : Fin d → ℝ := fun i => Real.sqrt
    (maternScalarTaylorResidualConstant (κ i) h q)
  let Cres : Fin d → ℝ := fun i =>
    max 1 (‖scalarFeature (κ i) h 0 (hκ i) hh‖⁻¹ * C0 i)
  have hC0 : ∀ i, 0 ≤ C0 i := by
    intro i
    exact Real.sqrt_nonneg _
  have hCres : ∀ i, 0 ≤ Cres i := by
    intro i
    exact le_trans (by norm_num) (le_max_left _ _)
  have hCres1 : ∀ i, 1 ≤ Cres i := by
    intro i
    exact le_max_left _ _
  have hres : ∀ i (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ N,
      ‖normalizedAxis (κ i) h t (hκ i) hh -
        (cumulativeLevelSpace (κ i) h q N (hκ i) hh).starProjection
          (normalizedAxis (κ i) h t (hκ i) hh)‖ ≤
        Cres i * (Real.rpow 2 (-h)) ^ N := by
    intro i t ht0 ht1 N
    by_cases hN : 1 ≤ N
    · have herr := scalarFeature_levelTaylor_residual_norm_le
        (κ i) h t N q (hκ i) hh ht0 ht1 (by exact_mod_cast hq) hN
      have hrate : (Real.rpow 2 (-h))^N =
          Real.rpow 2 (-h*(N:ℝ)) := by
        calc
          (Real.rpow 2 (-h))^N = (Real.rpow 2 (-h))^(N:ℝ) := by
            rw [← Real.rpow_natCast]
          _ = Real.rpow 2 (-h*(N:ℝ)) :=
            (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-h) (N:ℝ)).symm
      have hnorm := normalizedAxis_cumulative_residual_le_of_levelTaylorError
        (κ i) h t h (C0 i) N q (hκ i) hh hh (hC0 i) (by
          rw [hrate]
          simpa [maternScalarTaylorResidualConstant, C0] using herr)
      have hpow0 : 0 ≤ (Real.rpow 2 (-h))^N :=
        pow_nonneg (Real.rpow_nonneg (by norm_num) _) N
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (le_max_right 1 (‖scalarFeature (κ i) h 0 (hκ i) hh‖⁻¹ * C0 i)) hpow0)
    · have hN0 : N = 0 := by omega
      subst N
      let U := cumulativeLevelSpace (κ i) h q 0 (hκ i) hh
      have hmin :=
        BrownianSharp.AlignmentPaperCumulativeFiltration.projection_residual_le_of_candidate
          U 0 (normalizedAxis (κ i) h t (hκ i) hh) 0 U.zero_mem
      have hunit := normalizedAxis_norm (κ i) h t (hκ i) hh
      have hleone :
          ‖normalizedAxis (κ i) h t (hκ i) hh -
            U.starProjection (normalizedAxis (κ i) h t (hκ i) hh)‖ ≤ 1 := by
        simpa [U, hunit] using hmin
      have hrate0 : (Real.rpow 2 (-h))^0 = 1 := by simp
      simpa [hrate0] using hleone.trans (hCres1 i)
  exact rawMatern_grid_lower_bound_of_projection_residual hd κ c h h q
    hκ hc hh hh Cres hCres hres

end BrownianSharp.AlignmentPaperMaternGradedReverse
