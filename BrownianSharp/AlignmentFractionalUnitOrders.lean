import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.UniformSharpCertified
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.CameronMartinNativeConfinement
import BrownianSharp.CarlRateExtraction
import BrownianSharp.ExtendedStatements
import BrownianSharp.NativeCameronMartinEntropyUpper
import BrownianSharp.CameronMartinWidthCertified
import BrownianSharp.EntropyCoverInversion
import BrownianSharp.PeriodicEntropy
import BrownianSharp.TheoremDEntropyPacking
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import BrownianSharp.PeriodicMixedFinal
import BrownianSharp.AlignmentLatestStatements

noncomputable section
open HaarQuarter
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalUnitOrders
open BrownianSharp.AlignmentGaussianBochner
open BrownianSharp.CameronMartin

/-- At order one the Gamma-normalized causal tensor integral is exactly the
anchored integration operator used by the original Cameron--Martin result. -/
theorem fractionalIntegrationValue_one {d : ℕ}
    (g : UnitCubeL2 d) (x : BrownianCubeAnchor d) :
    Latest.fractionalIntegrationValue (fun _ : Fin d => (1:ℝ)) g x =
      unitCubeIntegrationPath g x := by
  have h := integratedFeatureField_fractionalIntegrationValue
    (fun _ : Fin d => 0) g x
  rw [integrateSheetFeatureField_naturalTensor,naturalTensorFeature_zero_eq_feature] at h
  have hemb : brownianCubeSpanEmbedding d (featureVector x) =
      (featureVector x : AmbientL2 d) := rfl
  rw [hemb] at h
  have h' : ⟪(featureVector x : AmbientL2 d),unitCubeZeroExtend g⟫ =
      Latest.fractionalIntegrationValue (fun _ : Fin d => (1:ℝ)) g x := by
    simpa [brownianCubeSpanEmbedding,unitCubeZeroExtendCLM] using h
  change _=⟪unitCubeZeroExtend g,(featureVector x : AmbientL2 d)⟫
  exact h'.symm.trans (real_inner_comm _ _)

/-- Exact set equality, with the same source unit ball and continuous
supremum-norm ambient space on both sides. -/
theorem fractionalIntegrationBall_one_eq_KdUnitCube (d : ℕ) :
    Latest.fractionalIntegrationBall (fun _ : Fin d => (1:ℝ))=KdUnitCube d := by
  ext f
  constructor
  · rintro ⟨g,hg,hgf⟩
    refine ⟨g,hg,?_⟩
    ext x
    exact (fractionalIntegrationValue_one g x).symm.trans (hgf x)
  · rintro ⟨g,hg,rfl⟩
    exact ⟨g,hg,fun x => fractionalIntegrationValue_one g x⟩

end BrownianSharp.AlignmentFractionalUnitOrders
