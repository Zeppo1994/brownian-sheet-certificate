import BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentFractionalEntropyTransfer

/-! The actual restriction from the reflected periodic path back to the cube.
The first half-period, rather than an unscaled torus representative, recovers
the original path. Taking real parts makes complex approximation centres
valid real continuous cube approximants without increasing their error. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction
open BrownianSharp.Torus BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension

private def halfCubeMap (d : ℕ) (t : BrownianCubeAnchor d) : UnitAddTorus (Fin d) :=
  fun i => ((t.val i / 2 : ℝ) : UnitAddCircle)

private theorem continuous_halfCubeMap (d : ℕ) : Continuous (halfCubeMap d) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (((continuous_apply i).comp continuous_subtype_val).div_const 2)

def halfCubeRealRestrictionLinear (d : ℕ) :
    C(UnitAddTorus (Fin d), ℂ) →ₗ[ℝ] C(BrownianCubeAnchor d, ℝ) where
  toFun f := ⟨fun t => (f (halfCubeMap d t)).re,
    Complex.continuous_re.comp (f.continuous.comp (continuous_halfCubeMap d))⟩
  map_add' f g := by ext t; simp
  map_smul' a f := by ext t; simp

theorem halfCubeRealRestrictionLinear_norm_le {d : ℕ}
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    ‖halfCubeRealRestrictionLinear d f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  exact (Complex.abs_re_le_norm (f (halfCubeMap d t))).trans
    (f.norm_coe_le_norm (halfCubeMap d t))

def halfCubeRealRestriction (d : ℕ) :
    C(UnitAddTorus (Fin d), ℂ) →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
  (halfCubeRealRestrictionLinear d).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using halfCubeRealRestrictionLinear_norm_le f)

theorem halfCubeRealRestriction_norm_le (d : ℕ) :
    ‖halfCubeRealRestriction d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem halfCubeRealRestriction_fold {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) :
    halfCubeRealRestriction d (complexifyContinuous (periodicFoldExtension f)) = f := by
  ext t
  change (periodicFoldExtension f (fun i => ((t.val i / 2 : ℝ) : UnitAddCircle)) : ℝ) = f t
  exact periodicFoldExtension_halfCube f t

/-- Contractive restriction transfers covers with the same index and radius,
including when centres lie outside the original real-valued path class. -/
theorem entropyNumber_le_of_contractive_image
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (hT : ‖T‖ ≤ 1) (K : Set X) (J : Set Y)
    (hsub : J ⊆ T '' K) (k : ℕ) :
    HaarQuarter.TheoremD.entropyNumber k J ≤ HaarQuarter.TheoremD.entropyNumber k K := by
  have hLip : LipschitzWith 1 T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
    exact (T.le_opNorm (x-y)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hT)
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ,rfl,hcover⟩
  apply sInf_le
  refine ⟨ρ,rfl,?_⟩
  have hmap := BrownianSharp.AlignmentFractionalEntropyTransfer.externalCoveringNumber_image_lipschitz
    T 1 hLip K ρ
  have hmap' : Metric.externalCoveringNumber ρ (T '' K) ≤
      Metric.externalCoveringNumber ρ K := by simpa only [one_mul] using hmap
  exact (Metric.externalCoveringNumber_mono_set (ε := ρ) hsub).trans (hmap'.trans hcover)

/-- A genuine source-class membership result suffices for the original
anchored image, because the folded path restricts exactly to its source. -/
theorem anchoredImage_entropy_le_of_fold_membership {d : ℕ} {p : ℝ}
    (hp : 1 < p) (K : Set C(UnitAddTorus (Fin d), ℂ))
    (hK : ∀ g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d), ‖g‖ ≤ 1 →
      complexifyContinuous (periodicFoldExtension (integrationPath p hp g)) ∈ K)
    (k : ℕ) :
    HaarQuarter.TheoremD.entropyNumber k (anchoredIntegrationLpImage d p) ≤
      HaarQuarter.TheoremD.entropyNumber k K := by
  apply entropyNumber_le_of_contractive_image (halfCubeRealRestriction d)
    (halfCubeRealRestriction_norm_le d) K (anchoredIntegrationLpImage d p) ?_ k
  rintro f ⟨g,hg,hf⟩
  refine ⟨complexifyContinuous (periodicFoldExtension (integrationPath p hp g)),hK g hg,?_⟩
  rw [halfCubeRealRestriction_fold]
  ext t
  exact hf t

end BrownianSharp.AlignmentPaperAnchoredLpCubeRestriction
