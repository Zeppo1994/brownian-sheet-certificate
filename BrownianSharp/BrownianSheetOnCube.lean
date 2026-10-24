import BrownianSharp.BrownianCubeSpan
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! A continuous-path Brownian sheet on the compact anchored cube. This is a
sample-path interface: it makes no assertion that a Brownian sheet can be
constructed from an ambient isonormal process. -/

open MeasureTheory ProbabilityTheory

namespace HaarQuarter

/-- The anchored unit cube is a nonempty compact parameter space. -/
instance brownianCubeAnchorCompactSpace (d : ℕ) :
    CompactSpace (BrownianCubeAnchor d) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : Fin d → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}
  have hc : IsCompact (Set.pi Set.univ
      (fun (_ : Fin d) => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun (_ : Fin d) =>
      isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have heq : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : Fin d) => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp [Set.pi]
  rw [heq]
  exact hc

instance brownianCubeAnchorNonempty (d : ℕ) : Nonempty (BrownianCubeAnchor d) := by
  exact ⟨⟨fun _ => 0, fun _ => ⟨by norm_num, by norm_num⟩⟩⟩

/-- Clamp each coordinate to `[0,1]`. -/
noncomputable def brownianCubeClamp (d : ℕ) :
    (Fin d → ℝ) → BrownianCubeAnchor d := fun x =>
  ⟨fun i => max 0 (min 1 (x i)), fun i => by
    constructor
    · exact le_max_left _ _
    · exact (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩

theorem continuous_brownianCubeClamp (d : ℕ) :
    Continuous (brownianCubeClamp d) := by
  apply Continuous.subtype_mk
  · fun_prop

@[simp] theorem brownianCubeClamp_apply_of_mem {d : ℕ}
    (x : BrownianCubeAnchor d) : brownianCubeClamp d x.val = x := by
  apply Subtype.ext
  funext i
  simp only [brownianCubeClamp]
  rcases x.property i with ⟨hx0, hx1⟩
  simp [max_eq_right hx0, min_eq_right hx1]

/-- Extend a continuous cube path to all of `ℝ^d` by coordinate clamping. -/
noncomputable def brownianCubeGlobalExtension {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) : C((Fin d → ℝ), ℝ) :=
  f.comp ⟨brownianCubeClamp d, continuous_brownianCubeClamp d⟩

@[simp] theorem brownianCubeGlobalExtension_apply {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) (x : Fin d → ℝ) :
    brownianCubeGlobalExtension f x = f (brownianCubeClamp d x) := rfl

theorem brownianCubeGlobalExtension_eq_on_cube {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) (x : BrownianCubeAnchor d) :
    brownianCubeGlobalExtension f x.val = f x := by
  simp

/-- A centered Brownian sheet with continuous sample paths on the anchored
unit cube. Gaussianity is stated in the standard finite-dimensional sense;
the covariance is the min-product kernel. The measurability field makes this
a genuine random element of the continuous-map space. -/
structure BrownianSheetOnCube (d : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) where
  path : Ω → C(BrownianCubeAnchor d, ℝ)
  measurable_path : Measurable path
  gaussian : IsGaussianProcess (fun x : BrownianCubeAnchor d => fun ω => path ω x) P
  mean_zero : ∀ x, ∫ ω, path ω x ∂P = 0
  covariance : ∀ x y,
    cov[fun ω => path ω x, fun ω => path ω y; P] = ∏ i, min (x.val i) (y.val i)

namespace BrownianSheetOnCube

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (B : BrownianSheetOnCube d Ω P)

/-- Coordinate process of a continuous-path sheet. -/
def eval (x : BrownianCubeAnchor d) (ω : Ω) : ℝ := B.path ω x

theorem measurable_eval (x : BrownianCubeAnchor d) : Measurable (B.eval x) := by
  exact (ContinuousMap.measurable_eval x).comp B.measurable_path

theorem eval_gaussian (x : BrownianCubeAnchor d) :
    HasGaussianLaw (B.eval x) P := by
  exact B.gaussian.hasGaussianLaw_eval x

theorem eval_mean_zero (x : BrownianCubeAnchor d) :
    ∫ ω, B.eval x ω ∂P = 0 := B.mean_zero x

theorem eval_covariance (x y : BrownianCubeAnchor d) :
    cov[B.eval x, B.eval y; P] = ∏ i, min (x.val i) (y.val i) := B.covariance x y

/-- The coordinate-clamped process on all of `ℝ^d`. -/
noncomputable def globalEval (x : Fin d → ℝ) (ω : Ω) : ℝ :=
  B.eval (brownianCubeClamp d x) ω

theorem globalEval_measurable (x : Fin d → ℝ) : Measurable (B.globalEval x) :=
  B.measurable_eval _

theorem globalPath_continuous (ω : Ω) :
    Continuous (fun x : Fin d → ℝ => B.globalEval x ω) := by
  exact (B.path ω).continuous.comp (continuous_brownianCubeClamp d)

theorem globalEval_eq_of_mem {x : Fin d → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (ω : Ω) :
    B.globalEval x ω = B.eval ⟨x, hx⟩ ω := by
  rw [globalEval, show brownianCubeClamp d x = ⟨x, hx⟩ from
    brownianCubeClamp_apply_of_mem ⟨x, hx⟩]

theorem globalGaussian :
    IsGaussianProcess (fun x : Fin d → ℝ => fun ω => B.globalEval x ω) P :=
  B.gaussian.comp_right (brownianCubeClamp d)

theorem globalEval_mean_zero (x : Fin d → ℝ) :
    ∫ ω, B.globalEval x ω ∂P = 0 := B.mean_zero (brownianCubeClamp d x)

theorem globalEval_covariance (x y : Fin d → ℝ) :
    cov[B.globalEval x, B.globalEval y; P] =
      ∏ i, min ((brownianCubeClamp d x).val i) ((brownianCubeClamp d y).val i) :=
  B.covariance (brownianCubeClamp d x) (brownianCubeClamp d y)

/-- The uniform-norm event is exactly the simultaneous pointwise bound used
in the sheet formulation. -/
theorem norm_le_iff_forall_eval (ω : Ω) (ε : ℝ) :
    ‖B.path ω‖ ≤ ε ↔ ∀ x, |B.eval x ω| ≤ ε := by
  simpa [eval, Real.norm_eq_abs] using
    (ContinuousMap.norm_le_of_nonempty (f := B.path ω) (M := ε))

theorem normEvent_eq_pointwiseEvent (ε : ℝ) :
    {ω | ‖B.path ω‖ ≤ ε} = {ω | ∀ x, |B.eval x ω| ≤ ε} := by
  ext ω
  exact B.norm_le_iff_forall_eval ω ε

end BrownianSheetOnCube

namespace BrownianSheetOnCube

/-- A coordinate-measurable continuous Gaussian sheet is a random element of
continuous functions on the cube. Thus the sample-path interface needs no
separate measurable-path assumption for the usual process formulation. -/
def ofProcess {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hMeasurable : ∀ x, Measurable (X x))
    (hContinuous : ∀ ω, Continuous (fun x => X x ω))
    (hGaussian : IsGaussianProcess X P)
    (hMean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hCovariance : ∀ x y, cov[X x, X y; P] =
      ∏ i, min (x.val i) (y.val i)) : BrownianSheetOnCube d Ω P where
  path ω := ⟨fun x => X x ω, hContinuous ω⟩
  measurable_path := ContinuousMap.measurable_iff_eval.mpr hMeasurable
  gaussian := hGaussian
  mean_zero := hMean
  covariance := hCovariance

@[simp] theorem ofProcess_eval {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hMeasurable : ∀ x, Measurable (X x))
    (hContinuous : ∀ ω, Continuous (fun x => X x ω))
    (hGaussian : IsGaussianProcess X P)
    (hMean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hCovariance : ∀ x y, cov[X x, X y; P] =
      ∏ i, min (x.val i) (y.val i)) (x : BrownianCubeAnchor d) (ω : Ω) :
    (ofProcess X hMeasurable hContinuous hGaussian hMean hCovariance).eval x ω =
      X x ω := rfl


noncomputable def aeContinuousNullCover
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω)) : Set Ω :=
  Classical.choose <| MeasureTheory.exists_measurable_superset_of_null
    (show P {ω | ¬ Continuous (fun x => X x ω)} = 0 from (ae_iff).1 hContinuous)

theorem aeContinuousNullCover_spec
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω)) :
    {ω | ¬ Continuous (fun x => X x ω)} ⊆ aeContinuousNullCover X hContinuous ∧
      MeasurableSet (aeContinuousNullCover X hContinuous) ∧
      P (aeContinuousNullCover X hContinuous) = 0 := by
  have hbad : P {ω | ¬ Continuous (fun x => X x ω)} = 0 := (ae_iff).1 hContinuous
  exact Classical.choose_spec
    (MeasureTheory.exists_measurable_superset_of_null hbad)

noncomputable def aeContinuousModification
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω)) :
    BrownianCubeAnchor d → Ω → ℝ := by
  classical
  exact fun x ω => if ω ∈ aeContinuousNullCover X hContinuous then 0 else X x ω

theorem aeContinuousModification_eq_ae
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω)) (x : BrownianCubeAnchor d) :
    X x =ᵐ[P] aeContinuousModification X hContinuous x := by
  classical
  have hcover := aeContinuousNullCover_spec X hContinuous
  have houtside : ∀ᵐ ω ∂P, ω ∉ aeContinuousNullCover X hContinuous := by
    apply (ae_iff).2
    simpa using hcover.2.2
  filter_upwards [houtside] with ω hω
  simp [aeContinuousModification, hω]

noncomputable def ofProcessAE
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hMeasurable : ∀ x, Measurable (X x))
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω))
    (hGaussian : IsGaussianProcess X P)
    (hMean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hCovariance : ∀ x y, cov[X x, X y; P] =
      ∏ i, min (x.val i) (y.val i)) : BrownianSheetOnCube d Ω P := by
  classical
  letI : IsProbabilityMeasure P := hGaussian.isProbabilityMeasure
  let Y := aeContinuousModification X hContinuous
  have hYAE : ∀ x, X x =ᵐ[P] Y x := by
    intro x
    simpa [Y] using aeContinuousModification_eq_ae X hContinuous x
  have hYMeasurable : ∀ x, Measurable (Y x) := by
    intro x
    change Measurable (fun ω =>
      if ω ∈ aeContinuousNullCover X hContinuous then 0 else X x ω)
    exact Measurable.ite (aeContinuousNullCover_spec X hContinuous).2.1
      measurable_const (hMeasurable x)
  have hYContinuous : ∀ ω, Continuous (fun x => Y x ω) := by
    intro ω
    by_cases hω : ω ∈ aeContinuousNullCover X hContinuous
    · simpa [Y, aeContinuousModification, hω] using
        (continuous_const : Continuous (fun _ : BrownianCubeAnchor d => (0 : ℝ)))
    · have hcont : Continuous (fun x => X x ω) := by
        by_contra hnot
        exact hω ((aeContinuousNullCover_spec X hContinuous).1 hnot)
      simpa [Y, aeContinuousModification, hω] using hcont
  have hYGaussian : IsGaussianProcess Y P :=
    hGaussian.congr (fun x => aeContinuousModification_eq_ae X hContinuous x)
  have hYMean : ∀ x, ∫ ω, Y x ω ∂P = 0 := by
    intro x
    rw [integral_congr_ae (aeContinuousModification_eq_ae X hContinuous x).symm]
    exact hMean x
  have hYCovariance : ∀ x y, cov[Y x, Y y; P] =
      ∏ i, min (x.val i) (y.val i) := by
    intro x y
    have hprod : (fun ω => Y x ω * Y y ω) =ᵐ[P]
        (fun ω => X x ω * X y ω) := by
      filter_upwards [hYAE x, hYAE y] with ω hx hy
      rw [← hx, ← hy]
    have hYx : MemLp (Y x) 2 P := (hYGaussian.hasGaussianLaw_eval x).memLp_two
    have hYy : MemLp (Y y) 2 P := (hYGaussian.hasGaussianLaw_eval y).memLp_two
    have hXx : MemLp (X x) 2 P := (hGaussian.hasGaussianLaw_eval x).memLp_two
    have hXy : MemLp (X y) 2 P := (hGaussian.hasGaussianLaw_eval y).memLp_two
    calc
      cov[Y x, Y y; P] =
          (∫ ω, Y x ω * Y y ω ∂P) -
            (∫ ω, Y x ω ∂P) * (∫ ω, Y y ω ∂P) :=
        covariance_eq_sub hYx hYy
      _ = (∫ ω, X x ω * X y ω ∂P) -
            (∫ ω, X x ω ∂P) * (∫ ω, X y ω ∂P) := by
        rw [integral_congr_ae hprod, hYMean x, hYMean y, hMean x, hMean y]
      _ = cov[X x, X y; P] := (covariance_eq_sub hXx hXy).symm
      _ = ∏ i, min (x.val i) (y.val i) := hCovariance x y
  exact ofProcess Y hYMeasurable hYContinuous hYGaussian hYMean hYCovariance


@[simp] theorem ofProcessAE_eval
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hMeasurable : ∀ x, Measurable (X x))
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω))
    (hGaussian : IsGaussianProcess X P)
    (hMean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hCovariance : ∀ x y, cov[X x, X y; P] =
      ∏ i, min (x.val i) (y.val i)) (x : BrownianCubeAnchor d) (ω : Ω) :
    (ofProcessAE X hMeasurable hContinuous hGaussian hMean hCovariance).eval x ω =
      aeContinuousModification X hContinuous x ω := by
  rfl

theorem ofProcessAE_eval_forall_ae
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : BrownianCubeAnchor d → Ω → ℝ)
    (hMeasurable : ∀ x, Measurable (X x))
    (hContinuous : ∀ᵐ ω ∂P, Continuous (fun x => X x ω))
    (hGaussian : IsGaussianProcess X P)
    (hMean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hCovariance : ∀ x y, cov[X x, X y; P] =
      ∏ i, min (x.val i) (y.val i)) :
    ∀ᵐ ω ∂P, ∀ x, (ofProcessAE X hMeasurable hContinuous hGaussian hMean hCovariance).eval x ω = X x ω := by
  classical
  let N := aeContinuousNullCover X hContinuous
  have hcover := aeContinuousNullCover_spec X hContinuous
  have houtside : ∀ᵐ ω ∂P, ω ∉ N := by
    apply (ae_iff).2
    simpa [N] using hcover.2.2
  filter_upwards [houtside] with ω hω
  intro x
  rw [ofProcessAE_eval]
  simp [aeContinuousModification, N, hω]

end BrownianSheetOnCube

end HaarQuarter
