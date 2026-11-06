import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.AlignmentScaledSetWidth
import BrownianSharp.Carl

/-! Actual contraction/restriction of finite approximating subspaces. This
is the target-space ideal step used after the Matérn periodic extension. -/
noncomputable section
open scoped ENNReal
open HaarQuarter.TheoremD.Width
namespace BrownianSharp.AlignmentPaperWidthContraction

universe u
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem kolmogorovWidth_contractive_image_le (R : X →L[ℝ] Y)
    (hR : ∀ x, ‖R x‖ ≤ ‖x‖) (K : Set X) (m : ℕ) :
    kolmogorovWidth (R '' K) m ≤ kolmogorovWidth K m := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  let b := kolmogorovWidth K m
  have hb : b ≠ ⊤ := ne_of_lt hfinite
  have hεr : 0 < (ε:ℝ) := hε
  have hpos : 0 < b.toReal+(ε:ℝ) := by positivity
  have hstrict : kolmogorovWidth K m < ENNReal.ofReal (b.toReal+(ε:ℝ)) := by
    change b < _
    conv_lhs => rw [← ENNReal.ofReal_toReal hb]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  obtain ⟨V,hV,happ⟩ := Carl.exists_width_subspace_pointwise_approximation K m hpos hstrict
  let W := V.map R.toLinearMap
  have hW : Module.rank ℝ W ≤ (m:Cardinal) := (rank_map_le R.toLinearMap V).trans hV
  have hp : ∀ y ∈ R '' K, ∃ w ∈ W, ‖y-w‖ ≤ b.toReal+(ε:ℝ) := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨v,hv⟩ := happ x hx
    refine ⟨R v,Submodule.mem_map.2 ⟨v,v.property,rfl⟩,?_⟩
    rw [← map_sub]
    exact (hR _).trans hv.le
  have hbound : kolmogorovWidth (R '' K) m ≤ ENNReal.ofReal (b.toReal+(ε:ℝ)) := by
    apply (iInf_le (fun U : {U : Submodule ℝ Y // Module.rank ℝ U ≤ (m:Cardinal)} =>
      approximationError (R '' K) U.val) ⟨W,hW⟩).trans
    exact AlignmentAmbientWidth.approximationError_le_of_pointwise _ _ hpos.le hp
  calc
    _ ≤ ENNReal.ofReal (b.toReal+(ε:ℝ)) := hbound
    _ = b+ε := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
        ENNReal.ofReal_toReal hb, ENNReal.ofReal_coe_nnreal]

/-- A bounded extension followed by a contraction transfers the source
width estimate to the original image ball. -/
theorem kolmogorovWidth_le_of_subset_contractive_scalar_image
    (R : X →L[ℝ] Y) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    {K : Set Y} {J : Set X} (A E : ℝ) (hA : 0 < A) (hE : 0 ≤ E)
    (hK : K ⊆ R '' AlignmentScaledSetWidth.scalarImage A J) (m : ℕ)
    (hJ : kolmogorovWidth J m ≤ ENNReal.ofReal E) :
    kolmogorovWidth K m ≤ ENNReal.ofReal (A*E) := by
  exact (AlignmentPeriodicUpperReduction.kolmogorovWidth_mono_set hK m).trans
    ((kolmogorovWidth_contractive_image_le R hR _ m).trans
      (AlignmentScaledSetWidth.kolmogorovWidth_scalarImage_le_of_bound J m A E hA hE hJ))

end BrownianSharp.AlignmentPaperWidthContraction
