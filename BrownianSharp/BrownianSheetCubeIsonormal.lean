import BrownianSharp.BrownianGaussianSpanExtension
import BrownianSharp.BrownianIsonormalL2Constructor
import BrownianSharp.BrownianSheetOnCube
import BrownianSharp.BrownianSheetCovarianceIsometry

open MeasureTheory ProbabilityTheory

namespace HaarQuarter

/-- The finite-dimensional Gaussian sheet on the unit cube induces a centered
isonormal family on the exact closed span of its anchored-box indicators. -/
theorem brownianSheetCube_isonormal_of_covariance_isometry
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P)
    (T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hT : ∀ x : BrownianCubeAnchor d,
      T ⟨brownianSheetBoxIndicatorLp x.val, brownianCubeBoxIndicator_mem x⟩ =
        ((B.gaussian.hasGaussianLaw_eval x).memLp_two).toLp (B.eval x))
    {ι : Type*} [Fintype ι] :
    ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω ι P,
      ∀ f : brownianCubeBoxSpan d,
        W.eval f =ᵐ[P] fun ω => T f ω := by
  classical
  let hB : ∀ x : BrownianCubeAnchor d, MemLp (B.eval x) 2 P :=
    fun x => (B.gaussian.hasGaussianLaw_eval x).memLp_two
  have hcenter : ∀ x : BrownianCubeAnchor d, ∫ ω, B.eval x ω ∂P = 0 :=
    B.eval_mean_zero
  have hjoint : ∀ s : Finset (BrownianCubeAnchor d),
      HasGaussianLaw (fun ω (x : s) => B.eval x.1 ω) P := by
    intro s
    change HasGaussianLaw (fun ω => s.restrict (fun x => B.path ω x)) P
    exact B.gaussian.hasGaussianLaw s
  let src : BrownianCubeAnchor d → Lp ℝ 2 P := fun x => (hB x).toLp (B.eval x)
  have himage (f : brownianCubeBoxSpan d) :
      T f ∈ (Submodule.span ℝ (Set.range src)).topologicalClosure := by
    exact closedSpan_isometry_image_mem
      (fun x : BrownianCubeAnchor d => brownianSheetBoxIndicatorLp x.val)
      src T hT f
  have hclosed := centeredGaussian_on_closedCoordinateSpan B.eval hB hjoint hcenter
  have hGaussian : ∀ f : brownianCubeBoxSpan d,
      HasGaussianLaw (fun ω => T f ω) P := by
    intro f
    exact (hclosed (T f) (himage f)).1
  have hmean : ∀ f : brownianCubeBoxSpan d, ∫ ω, T f ω ∂P = 0 := by
    intro f
    exact (hclosed (T f) (himage f)).2
  let W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω ι P :=
    isonormalGaussianFamily_of_l2_isometry (ι := ι) T hGaussian hmean
  refine ⟨W, ?_⟩
  intro f
  change l2MeasurableRepresentative (T f) =ᵐ[P] fun ω => T f ω
  exact (Lp.aestronglyMeasurable (T f)).ae_eq_mk.symm

/-- The sample-path interface supplies the covariance isometry needed by the
isonormal constructor, so the construction can be invoked without an ambient
white-noise extension. -/
theorem brownianSheetCube_exists_isonormal
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) {ι : Type*} [Fintype ι] :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω ι P,
        (∀ x : BrownianCubeAnchor d,
          T ⟨brownianSheetBoxIndicatorLp x.val, brownianCubeBoxIndicator_mem x⟩ =
            ((B.gaussian.hasGaussianLaw_eval x).memLp_two).toLp (B.eval x)) ∧
        (∀ f : brownianCubeBoxSpan d, W.eval f =ᵐ[P] fun ω => T f ω) := by
  have hB : ∀ x : BrownianCubeAnchor d, MemLp (B.eval x) 2 P :=
    fun x => (B.gaussian.hasGaussianLaw_eval x).memLp_two
  obtain ⟨T, hT⟩ := brownianSheet_covariance_isometry B.eval hB B.eval_mean_zero B.eval_covariance
  obtain ⟨W, hW⟩ :=
    brownianSheetCube_isonormal_of_covariance_isometry (ι := ι) B T hT
  exact ⟨T, W, hT, hW⟩

end HaarQuarter
