import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.AllThreeCertified
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

/-- The full entropy and width package in the all-unit-order fractional
subcase is inherited by an exact operator identification. -/
theorem unit_orders_entropy_width {d : ℕ} (hd : 2≤d) :
    ∃c C : ℝ,0<c ∧ 0<C ∧ ∃k₀ : ℕ,2≤k₀ ∧ ∀k : ℕ,k₀≤k →
      ENNReal.ofReal (c*logarithmicIndexRate 1
        (((d-1:ℕ):ℝ)+1/2) k)≤
        HaarQuarter.TheoremD.entropyNumber k
          (Latest.fractionalIntegrationBall (fun _ : Fin d => (1:ℝ))) ∧
      HaarQuarter.TheoremD.entropyNumber k
          (Latest.fractionalIntegrationBall (fun _ : Fin d => (1:ℝ)))≤
        ENNReal.ofReal (C*logarithmicIndexRate 1 (((d-1:ℕ):ℝ)+1/2) k) ∧
      ENNReal.ofReal (c*logarithmicIndexRate 1
        (((d-1:ℕ):ℝ)+1/2) k)≤
        HaarQuarter.TheoremD.Width.kolmogorovWidth
          (Latest.fractionalIntegrationBall (fun _ : Fin d => (1:ℝ))) k ∧
      HaarQuarter.TheoremD.Width.kolmogorovWidth
          (Latest.fractionalIntegrationBall (fun _ : Fin d => (1:ℝ))) k≤
        ENNReal.ofReal (C*logarithmicIndexRate 1 (((d-1:ℕ):ℝ)+1/2) k) := by
  obtain ⟨c,C,t₀,hc,hC,ht₀,hsmall,hcover,k₀,hk₀,h⟩ :=
    cameronMartinEntropyWidth_certified d hd
  have hexp : ((d-1:ℕ):ℝ)+1/2=(d:ℝ)-1/2 := by
    rw [Nat.cast_sub (by omega : 1≤d)]
    push_cast
    ring
  refine ⟨c,C,hc,hC,k₀,hk₀,?_⟩
  intro k hk
  simpa only [fractionalIntegrationBall_one_eq_KdUnitCube,hexp,cmIndexRate] using h k hk

end BrownianSharp.AlignmentFractionalUnitOrders
