import BrownianSharp.AlignmentFractionalSheetTensorFeature

/-! A concrete unit source feature for the actual fractional sheet. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalSheetUnitFeature
open AlignmentFractionalSheetTensorFeature AlignmentGaussianRates

def cubeOne (d : ℕ) : BrownianCubeAnchor d :=
  ⟨fun _ => 1, fun _ => ⟨by norm_num,by norm_num⟩⟩

theorem fractionalSheetFeature_one_inner {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) :
    ⟪fractionalSheetFeature H hH (cubeOne d),
      fractionalSheetFeature H hH (cubeOne d)⟫=1 := by
  rw [fractionalSheetFeature_gram]
  unfold fractionalSheetCovariance
  have he : ∀ i : Fin d,
      fractionalCoordinateCovariance (H i) ((cubeOne d).val i) ((cubeOne d).val i)=1 := by
    intro i
    simp [cubeOne,fractionalCoordinateCovariance,
      Real.zero_rpow (by linarith [(hH i).1] : 2*H i≠0)]
  simp_rw [he]
  simp

theorem fractionalSheetFeature_one_norm {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) :
    ‖fractionalSheetFeature H hH (cubeOne d)‖=1 := by
  have he := fractionalSheetFeature_one_inner H hH
  rw [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (fractionalSheetFeature H hH (cubeOne d))]

theorem fractionalSheetFeature_one_orthonormal {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) :
    Orthonormal ℝ (fun _ : Fin 1 => fractionalSheetFeature H hH (cubeOne d)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i=j := Subsingleton.elim i j
  subst j
  simpa using fractionalSheetFeature_one_inner H hH

end BrownianSharp.AlignmentFractionalSheetUnitFeature
