import BrownianSharp.AlignmentFractionalDensity
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open MeasureTheory
namespace BrownianSharp.AlignmentFractionalL2Semigroup
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalDensity

theorem profileToL2_denseRange : DenseRange profileToL2 := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  have hd := BoundedContinuousFunction.toLp_denseRange
    (E:=ℝ) (p:=2) μ ℝ (by norm_num : (2:ENNReal)≠⊤)
  apply hd.mono
  rintro g ⟨f,rfl⟩
  let F : C(UnitInterval,ℝ) :=
    ⟨fun t => f t.val, f.continuous.comp continuous_subtype_val⟩
  refine ⟨F,?_⟩
  apply Lp.ext
  have hF := profileToL2_coe F
  have hf := BoundedContinuousFunction.coeFn_toLp
    (E:=ℝ) (p:=2) μ ℝ f
  filter_upwards [hF,hf,ae_restrict_mem measurableSet_Icc] with t htF htf ht
  rw [htF,htf]
  change f (clipUnit t).val = f t
  congr 1
  simp [clipUnit,ht.1,ht.2]

/-- The actual scalar RL operators satisfy the semigroup law on all L²
sources, rather than only continuous profiles or polynomial atoms. -/
theorem fractionalRL_semigroup {a b : ℝ} (ha : 1/2<a) (hb : 1/2<b) :
    (fractionalOnC a ha).comp (fractionalRL b hb) =
      fractionalRL (a+b) (by linarith) := by
  have hd : Dense (Submodule.span ℝ (Set.range profileToL2) : Set UnitL2) :=
    profileToL2_denseRange.mono Submodule.subset_span
  apply ContinuousLinearMap.ext_on hd
  intro g hg
  rcases hg with ⟨F,rfl⟩
  change fractionalOnC a ha (fractionalOnC b hb F) =
    fractionalOnC (a+b) (by linarith) F
  exact congrArg (fun L => L F) (fractionalOnC_semigroup ha hb)

end BrownianSharp.AlignmentFractionalL2Semigroup
