import BrownianSharp.AlignmentPaperJointLowGradeCover

/-! Sharp scalar radius envelopes for actual grade covers. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointLowGradeCover
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperLpJointDvp

def dictionaryLogConstant (d : ℕ) : ℝ :=
  Real.log ((dictionaryGradePrefactor d:ℝ)+1) +
    Real.log (dictionaryGradeBase d:ℝ) + Real.log 129 + 1

theorem dictionaryLogConstant_pos (d : ℕ) : 0 < dictionaryLogConstant d := by
  have hU : (1:ℝ) ≤ (dictionaryGradePrefactor d:ℝ)+1 := by
    have h := Nat.cast_nonneg (dictionaryGradePrefactor d) (α := ℝ)
    linarith
  have hB : (1:ℝ) ≤ (dictionaryGradeBase d:ℝ) := by
    dsimp [dictionaryGradeBase]
    exact_mod_cast (one_le_pow₀ (n := d) (by norm_num : 1 ≤ (2:ℕ)))
  have h1 := Real.log_nonneg hU
  have h2 := Real.log_nonneg hB
  have h3 := Real.log_pos (by norm_num : (1:ℝ)<129)
  unfold dictionaryLogConstant
  linarith

theorem dictionaryLog_le_linear (d n : ℕ) :
    dictionaryLog d n ≤ dictionaryLogConstant d*(n+1:ℝ) := by
  let U : ℝ := dictionaryGradePrefactor d
  let B : ℝ := dictionaryGradeBase d
  have hU : 0 < U := by dsimp [U,dictionaryGradePrefactor]; positivity
  have hB : 1 ≤ B := by
    dsimp [B,dictionaryGradeBase]
    exact_mod_cast (one_le_pow₀ (n := d) (by norm_num : 1 ≤ (2:ℕ)))
  have hdim : (DictionaryDimension d n:ℝ) = U*B^n := by
    rw [dictionaryDimension_eq_grade_envelope]
    push_cast
    rfl
  have hdim' : (DictionaryDimension d n:ℝ)+1 ≤ (U+1)*B^n := by
    rw [hdim]
    nlinarith [one_le_pow₀ (n := n) hB]
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(DictionaryDimension d n:ℝ)+1) hdim'
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hlogU := Real.log_nonneg (by linarith : 1 ≤ U+1)
  have hlogB := Real.log_nonneg hB
  have hlog129 := Real.log_pos (by norm_num : (1:ℝ)<129)
  rw [Real.log_mul (by positivity : U+1≠0) (by positivity : B^n≠0),
    Real.log_pow] at hl
  unfold dictionaryLog dictionaryLogConstant
  change Real.log ((DictionaryDimension d n:ℝ)+1)+Real.log 129+1 ≤
    (Real.log (U+1)+Real.log B+Real.log 129+1)*(n+1)
  nlinarith [mul_nonneg hn hlogU, mul_nonneg hn hlog129.le]

/-- The full-rank scalar scale has the sharp grade decay, with one constant
chosen before the grade. -/
theorem exists_stageScale_fullRank_envelope {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      stageScale d n (gradeSeriesSourceRadius d p A n)*
        (JointSampleDimension d n:ℝ)^(-1/p) ≤
          K*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) := by
  let q : ℕ := d-1
  let cD : ℝ := (2:ℝ)^(3*d+1)/(Nat.factorial q:ℝ)
  let Cr : ℝ := Real.sqrt ((25/4:ℝ)^d)+1
  let L : ℝ := dictionaryLogConstant d
  let K : ℝ := 40*Real.sqrt 50*Cr*A*Real.sqrt L*cD^(-1/p)
  have hp0 : 0 < p := by linarith
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hCr : 0 < Cr := by dsimp [Cr]; positivity
  have hL : 0 < L := dictionaryLogConstant_pos d
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro n
  let m : ℝ := n+1
  have hm : 0 < m := by dsimp [m]; positivity
  have hq : (q:ℝ) = (d:ℝ)-1 := by
    dsimp [q]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hrow : jointRowBound d n ≤ Cr*m^((q:ℝ)/2) := by
    simpa [Cr,m,hq] using jointRowBound_le_polynomial (n:=n) hd
  have hlog : Real.sqrt (dictionaryLog d n) ≤ Real.sqrt L * Real.sqrt m := by
    calc
      _ ≤ Real.sqrt (L*m) := Real.sqrt_le_sqrt (dictionaryLog_le_linear d n)
      _ = _ := Real.sqrt_mul hL.le _
  have hDlo : cD*(2:ℝ)^n*m^q ≤ (JointSampleDimension d n:ℝ) := by
    simpa only [cD,q,m] using jointSampleDimension_lower_envelope (n:=n) (by omega : 1 ≤ d)
  have hnegative : -1/p ≤ (0:ℝ) :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
  have hDpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < cD*(2:ℝ)^n*m^q)
    hDlo hnegative
  have hDfactor : (cD*(2:ℝ)^n*m^q)^(-1/p) =
      cD^(-1/p)*(2:ℝ)^(-(n:ℝ)/p)*m^(-(q:ℝ)/p) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hcD.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ← Real.rpow_natCast m q, ← Real.rpow_mul hm.le]
    rw [show (n:ℝ)*(-1/p) = -(n:ℝ)/p by ring,
      show (q:ℝ)*(-1/p) = -(q:ℝ)/p by ring]
  rw [hDfactor] at hDpow
  have hB : 0 < gradeSeriesSourceRadius d p A n := by
    unfold gradeSeriesSourceRadius
    positivity
  have hprod : stageScale d n (gradeSeriesSourceRadius d p A n)*
      (JointSampleDimension d n:ℝ)^(-1/p) ≤
      (40*Real.sqrt 50*(Cr*m^((q:ℝ)/2))*gradeSeriesSourceRadius d p A n*
        (Real.sqrt L*Real.sqrt m))*
        (cD^(-1/p)*(2:ℝ)^(-(n:ℝ)/p)*m^(-(q:ℝ)/p)) := by
    unfold stageScale
    gcongr
  apply hprod.trans_eq
  unfold gradeSeriesSourceRadius
  change (40*Real.sqrt 50*(Cr*m^((q:ℝ)/2))*
    (A*(2:ℝ)^(-(1-1/p)*(n:ℝ))*m^((q:ℝ)*(1/p-1/2)))*
    (Real.sqrt L*Real.sqrt m))*
    (cD^(-1/p)*(2:ℝ)^(-(n:ℝ)/p)*m^(-(q:ℝ)/p)) =
    K*(2:ℝ)^(-(n:ℝ))*Real.sqrt m
  have htwo : (2:ℝ)^(-(1-1/p)*(n:ℝ))*(2:ℝ)^(-(n:ℝ)/p) =
      (2:ℝ)^(-(n:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hmpow : m^((q:ℝ)/2)*m^((q:ℝ)*(1/p-1/2))*m^(-(q:ℝ)/p) = 1 := by
    rw [← Real.rpow_add hm, ← Real.rpow_add hm]
    have he : (q:ℝ)/2+(q:ℝ)*(1/p-1/2)+ -(q:ℝ)/p = 0 := by ring
    rw [he,Real.rpow_zero]
  calc
    _ = (40*Real.sqrt 50*Cr*A*Real.sqrt L*cD^(-1/p))*
        ((2:ℝ)^(-(1-1/p)*(n:ℝ))*(2:ℝ)^(-(n:ℝ)/p))*
        (m^((q:ℝ)/2)*m^((q:ℝ)*(1/p-1/2))*m^(-(q:ℝ)/p))*Real.sqrt m := by ring
    _ = K*(2:ℝ)^(-(n:ℝ))*Real.sqrt m := by rw [htwo,hmpow]; simp [K]

theorem jointSampleDimension_pos_of_dimension_pos {d n : ℕ} (hd : 0 < d) :
    0 < JointSampleDimension d n := by
  rw [jointSampleDimension_eq_grid_formula, BrownianSharp.shape_card d n hd]
  exact Nat.mul_pos (by positivity) (Nat.choose_pos (by omega))

/-- Actual maximal-rank covers at the sharp low-grade envelope, with one
constant chosen before every grade and every member of the source class. -/
theorem exists_lowGrade_cover_envelope {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∃ C : Set C(UnitAddTorus (Fin d),ℂ), C.Finite ∧
        Metric.IsCover (Real.toNNReal (K*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)))
          (decodedJointLpFeatureImage (d := d) (n := n) p
            (gradeSeriesSourceRadius d p A n)) C ∧
        C.encard ≤ ((2 ^ Nat.ceil
          (lowGradeCodingConstant*(JointSampleDimension d n:ℝ)) : ℕ) : ℕ∞) := by
  obtain ⟨K,hK,hscale⟩ := exists_stageScale_fullRank_envelope hd hp hA
  let L : ℝ := 24*(5:ℝ)^d*(2:ℝ)^(1/p)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L*K,mul_pos hL hK,?_⟩
  intro n
  have hD := jointSampleDimension_pos_of_dimension_pos (n:=n) (by omega : 0 < d)
  have hB : 0 < gradeSeriesSourceRadius d p A n := by
    unfold gradeSeriesSourceRadius
    positivity
  obtain ⟨C,hC,hcover,hcard⟩ := exists_maximalDyadic_decodedGrade_cover hp hp2 hB hD
  refine ⟨C,hC,?_,hcard⟩
  have hrad := maximalDyadic_decodedGrade_radius_le hp hB hD
  have hbound :
      (decodedGradeDyadicRadius d n p (gradeSeriesSourceRadius d p A n)
        (Nat.log2 (JointSampleDimension d n)) : ℝ) ≤
      (L*K)*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ) := by
    apply hrad.trans
    have hh := mul_le_mul_of_nonneg_left (hscale n) hL.le
    simpa [L,mul_assoc] using hh
  have hNN : decodedGradeDyadicRadius d n p (gradeSeriesSourceRadius d p A n)
      (Nat.log2 (JointSampleDimension d n)) ≤
        Real.toNNReal ((L*K)*(2:ℝ)^(-(n:ℝ))*Real.sqrt (n+1:ℝ)) := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hbound
  intro f hf
  obtain ⟨c,hc,hdist⟩ := hcover hf
  exact ⟨c,hc,hdist.trans (ENNReal.coe_le_coe.mpr hNN)⟩

end BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
