import BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
import BrownianSharp.AlignmentPaperJointRefinementBinaryBudget

/-! Fixed low-grade target radii and actual refined grade-cover families. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily
open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointGradeRefinement
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperLpJointDvp

def lowTargetRadius (N n : ℕ) : ℝ :=
  (2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ)*(2:ℝ)^(-((N-n:ℕ):ℝ))

theorem lowTargetRadius_pos (N n : ℕ) : 0 < lowTargetRadius N n := by
  unfold lowTargetRadius
  positivity

/-- The sharp coarse radius needs only an exponentially growing refinement
ratio, measured in the distance of the grade below the splitting grade. -/
theorem lowGrade_refinement_ratio_le {N n : ℕ} (hn : n ≤ N)
    {K ε : ℝ} (hK : 0 < K)
    (hε : ε ≤ K*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)) :
    ε / lowTargetRadius N n ≤ K*(2:ℝ)^(2*((N-n:ℕ):ℝ)) := by
  have hη := lowTargetRadius_pos N n
  apply (div_le_iff₀ hη).2
  have hsqrt : Real.sqrt (n+1:ℝ) ≤ Real.sqrt (N+1:ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hn 1
  have hpow : (2:ℝ)^(2*((N-n:ℕ):ℝ))*
      ((2:ℝ)^(-(N:ℝ))*(2:ℝ)^(-((N-n:ℕ):ℝ))) =
        (2:ℝ)^(-(n:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    rw [Nat.cast_sub hn]
    ring
  calc
    ε ≤ K*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) := hε
    _ ≤ K*(2:ℝ)^(-(n:ℝ))*Real.sqrt (N+1:ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = K*(2:ℝ)^(2*((N-n:ℕ):ℝ))*lowTargetRadius N n := by
      unfold lowTargetRadius
      calc
        _ = K*((2:ℝ)^(2*((N-n:ℕ):ℝ))*
          ((2:ℝ)^(-(N:ℝ))*(2:ℝ)^(-((N-n:ℕ):ℝ))))*Real.sqrt (N+1:ℝ) := by
            rw [hpow]
        _ = _ := by ring

/-- Low grades have fixed finite refined covers at geometrically distributed
error radii. All covers are chosen before any member of the series class. -/
theorem exists_lowGrade_refined_cover_family {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ Cbit : ℝ, 0 < Cbit ∧ ∀ N : ℕ,
      ∃ C : Fin (N+1) → Set C(UnitAddTorus (Fin d),ℂ), ∀ i : Fin (N+1),
        (C i).Finite ∧
        Metric.IsCover (NNReal.mk (lowTargetRadius N i.val)
          (lowTargetRadius_pos N i.val).le)
          (decodedJointLpFeatureImage (d := d) (n := i.val) p
            (gradeSeriesSourceRadius d p A i.val)) (C i) ∧
        (C i).encard ≤ ((2 ^ Nat.ceil (Cbit*(JointSampleDimension d i.val:ℝ)*
          ((N-i.val:ℕ)+1:ℝ)) : ℕ) : ℕ∞) := by
  classical
  obtain ⟨K,hK,hcoarse⟩ := exists_lowGrade_cover_envelope hd hp hp2 hA
  obtain ⟨Cbit,hCbit,hbinary⟩ :=
    BrownianSharp.AlignmentPaperJointRefinementBinaryBudget.exists_joint_refinement_binary_budget
      BrownianSharp.AlignmentPaperJointLowGradeCover.lowGradeCodingConstant_pos hK
  refine ⟨Cbit,hCbit,?_⟩
  intro N
  have hper (i : Fin (N+1)) :
      ∃ C : Set C(UnitAddTorus (Fin d),ℂ), C.Finite ∧
        Metric.IsCover (NNReal.mk (lowTargetRadius N i.val)
          (lowTargetRadius_pos N i.val).le)
          (decodedJointLpFeatureImage (d := d) (n := i.val) p
            (gradeSeriesSourceRadius d p A i.val)) C ∧
        C.encard ≤ ((2 ^ Nat.ceil (Cbit*(JointSampleDimension d i.val:ℝ)*
          ((N-i.val:ℕ)+1:ℝ)) : ℕ) : ℕ∞) := by
    obtain ⟨C,hC,hcover,hcard⟩ := hcoarse i.val
    let ε : ℝ≥0 := Real.toNNReal (K*(2:ℝ)^(-(i.val:ℝ))*Real.sqrt (i.val+1:ℝ))
    have hη := lowTargetRadius_pos N i.val
    obtain ⟨D,hD,hcoverD,hcountD⟩ := exists_decodedGrade_refined_cover
      (d := d) (n := i.val) (p := p)
      (B := gradeSeriesSourceRadius d p A i.val) (ε := ε)
      (η := lowTargetRadius N i.val) hC hcover hη
    have hε : (ε:ℝ) = K*(2:ℝ)^(-(i.val:ℝ))*Real.sqrt (i.val+1:ℝ) := by
      exact Real.coe_toNNReal _ (by positivity)
    have hratio := lowGrade_refinement_ratio_le (Nat.le_of_lt_succ i.isLt) hK hε.le
    have hratioNat : (ε:ℝ)/lowTargetRadius N i.val ≤
        K*(2:ℝ)^(2*(N-i.val)) := by
      rw [← Real.rpow_natCast]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
    have hdim := jointSampleDimension_pos_of_dimension_pos (n:=i.val) (by omega : 0 < d)
    have hb := hbinary (JointSampleDimension d i.val) hdim (N-i.val)
      (ε:ℝ) (lowTargetRadius N i.val) ε.coe_nonneg hη hratioNat
    refine ⟨D,hD,hcoverD,hcountD.trans ?_⟩
    calc
      _ ≤ (((2 ^ Nat.ceil
          (BrownianSharp.AlignmentPaperJointLowGradeCover.lowGradeCodingConstant*
            (JointSampleDimension d i.val:ℝ)) : ℕ) : ℕ∞) *
          ↑(Nat.ceil ((1+4*(ε:ℝ)/lowTargetRadius N i.val)^JointSampleDimension d i.val))) :=
        mul_le_mul hcard le_rfl (by positivity) (by positivity)
      _ ≤ _ := by exact_mod_cast hb
  choose C hC using hper
  exact ⟨C,hC⟩

end BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily
