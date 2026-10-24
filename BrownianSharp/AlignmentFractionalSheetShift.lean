import BrownianSharp.AlignmentFractionalSheetEntropy
import BrownianSharp.AlignmentFractionalSheetUnitFeature
import BrownianSharp.AlignmentFractionalSheetGridConfinement
import BrownianSharp.AlignmentGaussianFeatureShift
import BrownianSharp.AlignmentGaussianGridLimit
import BrownianSharp.AlignmentGaussianEntropySmallBall
import Mathlib.MeasureTheory.Measure.Map

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalSheetShift

open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentFractionalSheetGridConfinement
open BrownianSharp.AlignmentFractionalSheetPositiveSource
open BrownianSharp.AlignmentFractionalSheetEntropy
open BrownianSharp.AlignmentFractionalSheetUnitFeature
open BrownianSharp.AlignmentGaussianFeatureShift
open BrownianSharp.AlignmentGaussianGridLimit
open BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentCompactFeatureBall

private def sheetCorner (d : ℕ) : BrownianCubeAnchor d :=
  ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩⟩

private theorem fractionalSheetFeature_corner_norm_sq {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) :
    ‖fractionalSheetFeature H hH (sheetCorner d)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa [sheetCorner, cubeOne] using fractionalSheetFeature_one_inner H hH

/-- Law of the actual continuous fractional-sheet path. -/
def fractionalSheetLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (B : FractionalBrownianSheetOnCube d Ω P) :
    Measure C(BrownianCubeAnchor d, ℝ) := P.map B.path

/-- Cameron–Martin shift lower bound for the actual fractional-sheet path law.
Finite grids use the actual centered Gaussian covariance and its MvN feature
Gram matrix; compactness of the parameter cube then passes the inequality to
closed balls in the uniform path norm. -/
theorem fractionalSheetLaw_ball_shift_lower {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : FractionalBrownianSheetOnCube d Ω P)
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1) (hBH : B.H = H)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : C(BrownianCubeAnchor d, ℝ))
    (hx : x ∈ featureBall (fractionalSheetFeature H hH)) :
    ENNReal.ofReal (Real.exp (-(R^2)/2)) *
        fractionalSheetLaw B (Metric.closedBall 0 ε) ≤
      fractionalSheetLaw B (Metric.closedBall (R • x) ε) := by
  classical
  rcases hx with ⟨g, hg, hx⟩
  let μ := fractionalSheetLaw B
  let f : C(BrownianCubeAnchor d,ℝ) := R • x
  have hfinite : ∀ S : Finset (BrownianCubeAnchor d),
      ENNReal.ofReal (Real.exp (-(R^2)/2)) *
        P {ω | ∀ t ∈ S, |B.path ω t| ≤ ε} ≤
      P {ω | ∀ t ∈ S, |B.path ω t - f t| ≤ ε} := by
    intro S
    let I := {t : BrownianCubeAnchor d // t ∈ S}
    let X : Ω → I → ℝ := fun ω t => B.path ω t.1
    let v : I → AlignmentFractionalSheetTensorFeature.FullProductL2 d := fun t => fractionalSheetFeature H hH t.1
    let e : Fin 1 → AlignmentFractionalSheetTensorFeature.FullProductL2 d := fun _ => fractionalSheetFeature H hH (sheetCorner d)
    have he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0 := by
      intro i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      rw [if_pos rfl, real_inner_self_eq_norm_sq]
      exact fractionalSheetFeature_corner_norm_sq H hH
    have hX : HasGaussianLaw (fun ω t => X ω t) P := by
      simpa [X] using fractionalSheet_grid_hasGaussianLaw B (fun t : I => t.1)
    have hmean : ∀ t, ∫ ω, X ω t ∂P = 0 := by
      intro t
      exact B.mean_zero t.1
    have hcov : ∀ s t, covariance (fun ω => X ω s) (fun ω => X ω t) P =
        ⟪v s, v t⟫ := by
      intro s t
      rw [show (fun ω => X ω s) = fun ω => B.path ω s.1 by rfl,
        show (fun ω => X ω t) = fun ω => B.path ω t.1 by rfl,
        B.covariance, hBH, fractionalSheetFeature_gram]
    have hgrid := finiteGaussian_gram_shift_lower X e v hX hmean hcov he (R • g) ε
    have hshift : ∀ t : I,
        ⟪v t, R • g⟫ = f t.1 := by
      intro t
      rw [inner_smul_right]
      change R * ⟪v t, g⟫ = R * x t.1
      rw [real_inner_comm]
      have hx' := congrArg (fun q : C(BrownianCubeAnchor d,ℝ) => q t.1) hx
      simpa [featurePath] using congrArg (fun z : ℝ => R * z) hx'
    have hshifted : {ω | ∀ t : I, |X ω t - ⟪v t, R • g⟫| ≤ ε} =
        {ω | ∀ t ∈ S, |B.path ω t - f t| ≤ ε} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h t ht
        have := h ⟨t,ht⟩
        simpa [X, hshift] using this
      · intro h t
        simpa [X, hshift] using h t.1 t.2
    have hcenter : {ω | ∀ t : I, |X ω t| ≤ ε} =
        {ω | ∀ t ∈ S, |B.path ω t| ≤ ε} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h t ht
        simpa [X] using h ⟨t, ht⟩
      · intro h t
        simpa [X] using h t.1 t.2
    rw [hshifted, hcenter] at hgrid
    have hnorm : ‖R • g‖ ^ 2 ≤ R ^ 2 := by
      have hn : ‖R • g‖ = R * ‖g‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      rw [hn]
      have hmul : R * ‖g‖ ≤ R := by
        calc R * ‖g‖ ≤ R * 1 := mul_le_mul_of_nonneg_left hg hR.le
          _ = R := by ring
      nlinarith [hmul, norm_nonneg g,
        mul_nonneg hR.le (norm_nonneg g), sq_nonneg (R - R * ‖g‖)]
    have hexp : ENNReal.ofReal (Real.exp (-(R^2)/2)) ≤
        ENNReal.ofReal (Real.exp (-‖R • g‖^2/2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [hnorm]
    have hmul : ENNReal.ofReal (Real.exp (-(R^2)/2)) *
        P {ω | ∀ t ∈ S, |B.path ω t| ≤ ε} ≤
        ENNReal.ofReal (Real.exp (-‖R • g‖^2/2)) *
        P {ω | ∀ t ∈ S, |B.path ω t| ≤ ε} :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    exact hmul.trans hgrid
  letI : Nonempty (BrownianCubeAnchor d) :=
    ⟨⟨0, fun _ => ⟨by norm_num, by norm_num⟩⟩⟩
  let points : ℕ → BrownianCubeAnchor d := TopologicalSpace.denseSeq _
  have hdense : DenseRange points := TopologicalSpace.denseRange_denseSeq _
  have hcoord : ∀ t, Measurable (fun ω => B.path ω t) := by
    intro t
    exact (continuous_eval_const t).measurable.comp B.measurable_path
  have hgrid := finite_grid_mass_lower_to_uniform_mass_lower P points hdense
    B.path hcoord f ε hε.le
    (ENNReal.ofReal (Real.exp (-(R^2)/2))) hfinite
  have h0 : MeasurableSet (Metric.closedBall (0 : C(BrownianCubeAnchor d,ℝ)) ε) :=
    measurableSet_closedBall
  have hxball : MeasurableSet (Metric.closedBall f ε) := measurableSet_closedBall
  have hmass0 : μ (Metric.closedBall 0 ε) = P {ω | ‖B.path ω‖ ≤ ε} := by
    change (P.map B.path) (Metric.closedBall 0 ε) = _
    rw [Measure.map_apply B.measurable_path h0]
    congr 1
  have hmassx : μ (Metric.closedBall f ε) = P {ω | ‖B.path ω-f‖ ≤ ε} := by
    change (P.map B.path) (Metric.closedBall f ε) = _
    rw [Measure.map_apply B.measurable_path hxball]
    congr 1
    ext ω
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hmass0, hmassx]
  simpa [μ, f, Metric.mem_closedBall, dist_eq_norm] using hgrid

end BrownianSharp.AlignmentFractionalSheetShift
