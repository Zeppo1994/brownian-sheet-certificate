import BrownianSharp.FiniteHaarGridSpan
import BrownianSharp.FiniteHaarGradeEnergy
import BrownianSharp.AlignmentGaussianHaarTail

/-! Finite-grid variance control after grade-dependent Gaussian scaling. -/

open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianHaarProjection
open HaarQuarter CameronMartin

noncomputable section

def gradeScale (N n : ℕ) : ℝ :=
  if n ≤ N then 1 / (2 : ℝ) ^ (N - n) else 1

theorem gradeScale_nonneg (N n : ℕ) : 0 ≤ gradeScale N n := by
  unfold gradeScale
  split_ifs <;> positivity

theorem gradeScale_le_one (N n : ℕ) : gradeScale N n ≤ 1 := by
  unfold gradeScale
  split_ifs with h
  · have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (N - n) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ (N - n))
    exact (div_le_one (by positivity)).2 hp
  · norm_num

def gradeScaledFeature {d N M : ℕ} (x : brownianCubeBoxSpan d) :
    brownianCubeBoxSpan d :=
  ∑ a : FiniteHaarIndex d M,
    (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) •
      finiteHaarVector a

def gradeScaledBoxFeature {d N M : ℕ} (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : brownianCubeBoxSpan d :=
  gradeScaledFeature (N := N) (M := M)
    ⟨brownianSheetBoxIndicatorLp t, brownianCubeBoxIndicator_mem ⟨t, ht⟩⟩

theorem gradeScaledFeature_norm_sq {d N M : ℕ}
    (x : brownianCubeBoxSpan d) :
    ‖gradeScaledFeature (N := N) (M := M) x‖ ^ 2 =
      ∑ a : FiniteHaarIndex d M,
        (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) ^ 2 := by
  classical
  have horth : Orthonormal ℝ (finiteHaarVector (d := d) (N := M)) :=
    orthonormal_iff_ite.mpr finiteHaarVector_orthonormal
  calc
    ‖gradeScaledFeature (N := N) (M := M) x‖ ^ 2 =
        ⟪gradeScaledFeature (N := N) (M := M) x,
          gradeScaledFeature (N := N) (M := M) x⟫ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ a : FiniteHaarIndex d M,
        (gradeScale N (finiteHaarGrade a) *
          ⟪x, finiteHaarVector a⟫) ^ 2 := by
      change ⟪∑ a : FiniteHaarIndex d M,
          (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) •
            finiteHaarVector a,
        ∑ a : FiniteHaarIndex d M,
          (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) •
            finiteHaarVector a⟫ = _
      rw [horth.inner_sum]
      simp only [starRingEnd_apply, star_trivial]
      ring_nf

private theorem finiteHaarGrade_le {d M : ℕ} (a : FiniteHaarIndex d M) :
    finiteHaarGrade a ≤ d * M := by
  unfold finiteHaarGrade
  calc
    (∑ i : Fin d, finiteHaarAxisGrade (a i)) ≤ ∑ _i : Fin d, M := by
      apply Finset.sum_le_sum
      intro i hi
      cases h : a i with
      | none => simp [finiteHaarAxisGrade]
      | some p =>
          rcases p with ⟨r, j⟩
          simp only [finiteHaarAxisGrade]
          have hr := r.isLt
          omega
    _ = d * M := by simp

private def gradeEquiv {d M : ℕ} :
    FiniteHaarIndex d M ≃
      Σ n : Fin (d * M + 1), FiniteHaarGradeLayer d M n.val where
  toFun a := ⟨⟨finiteHaarGrade a, Nat.lt_succ_of_le (finiteHaarGrade_le a)⟩,
    ⟨a, rfl⟩⟩
  invFun p := p.2.1
  left_inv a := rfl
  right_inv p := by
    rcases p with ⟨n, ⟨a, hn⟩⟩
    let n' : Fin (d * M + 1) :=
      ⟨finiteHaarGrade a, Nat.lt_succ_of_le (finiteHaarGrade_le a)⟩
    have heq : n' = n := Fin.ext hn
    subst n
    rfl

private theorem scaled_feature_norm_sq_eq_grade_sum {d N M : ℕ}
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ‖gradeScaledFeature (N := N) (M := M)
        (⟨brownianSheetBoxIndicatorLp t,
          brownianCubeBoxIndicator_mem ⟨t, ht⟩⟩ : brownianCubeBoxSpan d)‖ ^ 2 =
      ∑ n : Fin (d * M + 1),
        gradeScale N n.val ^ 2 *
          ∑ a : FiniteHaarGradeLayer d M n.val,
            finiteHaarGridCoefficient a.1 t ht ^ 2 := by
  classical
  let x : brownianCubeBoxSpan d :=
    ⟨brownianSheetBoxIndicatorLp t, brownianCubeBoxIndicator_mem ⟨t, ht⟩⟩
  rw [gradeScaledFeature_norm_sq]
  rw [Fintype.sum_equiv (gradeEquiv (d := d) (M := M))
    (fun a : FiniteHaarIndex d M =>
      (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) ^ 2)
    (fun p : Σ n : Fin (d * M + 1), FiniteHaarGradeLayer d M n.val =>
      gradeScale N p.1.val ^ 2 *
        finiteHaarGridCoefficient p.2.1 t ht ^ 2)
    (by
      intro a
      rw [show ⟪x, finiteHaarVector a⟫ =
        finiteHaarGridCoefficient a t ht by
          dsimp [x, finiteHaarGridCoefficient]
          rw [real_inner_comm]
          ]
      simp [gradeEquiv]
      ring_nf)]
  rw [Fintype.sum_sigma]
  change (∑ n : Fin (d * M + 1),
      ∑ a : FiniteHaarGradeLayer d M n.val,
        gradeScale N n.val ^ 2 * finiteHaarGridCoefficient a.1 t ht ^ 2) = _
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mul_sum]

theorem grade_scaled_feature_variance_le {d N M : ℕ} (hd : 0 < d)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ‖gradeScaledFeature (N := N) (M := M)
        (⟨brownianSheetBoxIndicatorLp t,
          brownianCubeBoxIndicator_mem ⟨t, ht⟩⟩ : brownianCubeBoxSpan d)‖ ^ 2 ≤
      ∑ n : Fin (d * M + 1),
        gradeScale N n.val ^ 2 *
          ((Nat.choose (n.val + d - 1) (d - 1) : ℝ) /
            (2 : ℝ) ^ n.val) := by
  rw [scaled_feature_norm_sq_eq_grade_sum t ht]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left
  · exact finiteHaarGrade_grid_energy_le hd t ht
  · exact sq_nonneg _

theorem gradeScaledFeature_norm_le {d N M : ℕ} (x : brownianCubeBoxSpan d) :
    ‖gradeScaledFeature (N := N) (M := M) x‖ ≤ ‖x‖ := by
  classical
  have hsq := gradeScaledFeature_norm_sq (N := N) (M := M) x
  have horth : Orthonormal ℝ (finiteHaarVector (d := d) (N := M)) :=
    orthonormal_iff_ite.mpr finiteHaarVector_orthonormal
  have hbessel := horth.sum_inner_products_le (s := Finset.univ) x
  have hsum : ∑ a : FiniteHaarIndex d M,
      (gradeScale N (finiteHaarGrade a) * ⟪x, finiteHaarVector a⟫) ^ 2 ≤
        ∑ a : FiniteHaarIndex d M, ⟪finiteHaarVector a, x⟫ ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    rw [real_inner_comm]
    have hw0 := gradeScale_nonneg N (finiteHaarGrade a)
    have hw1 := gradeScale_le_one N (finiteHaarGrade a)
    have hwSq : (gradeScale N (finiteHaarGrade a)) ^ 2 ≤ 1 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hwSq
      (sq_nonneg (⟪finiteHaarVector a, x⟫ : ℝ))
    nlinarith [hmul]
  have hnorm : ∑ a : FiniteHaarIndex d M,
      ⟪finiteHaarVector a, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using hbessel
  have hsqle : ‖gradeScaledFeature (N := N) (M := M) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq]
    exact hsum.trans hnorm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsqle

theorem gradeScaledFeature_sub_norm_le {d N M : ℕ}
    (x y : brownianCubeBoxSpan d) :
    ‖gradeScaledFeature (N := N) (M := M) x -
      gradeScaledFeature (N := N) (M := M) y‖ ≤ ‖x-y‖ := by
  have hlinear : gradeScaledFeature (N := N) (M := M) x -
      gradeScaledFeature (N := N) (M := M) y =
      gradeScaledFeature (N := N) (M := M) (x-y) := by
    simp only [gradeScaledFeature, inner_sub_left, sub_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_sub, sub_smul]
    module
  rw [hlinear]
  exact gradeScaledFeature_norm_le (N := N) (M := M) (x-y)

theorem gradeScaledFeature_continuous {d N M : ℕ} :
    Continuous (gradeScaledFeature (d := d) (N := N) (M := M)) := by
  unfold gradeScaledFeature
  fun_prop

end
end BrownianSharp.AlignmentGaussianHaarProjection
