import BrownianSharp.AlignmentPaperFractionalCarlRoute
import BrownianSharp.AlignmentFractionalSheetShift
import BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice
import BrownianSharp.AlignmentGaussianActualFractionalUpperLog

/-! Connect the explicit scalar fractional preimage contract to isotropic
feature entropy, actual-sheet lower logarithmic small balls, and the
minimum-coordinate restriction for unequal Hurst profiles. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperFractionalSheetScalarLower

open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalSheetPositiveSource
open BrownianSharp.AlignmentFractionalSheetPositive
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalSheetShift
open BrownianSharp.AlignmentFractionalEntropyTransfer
open BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentCompactFeatureBall
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperFractionalEntropyRoute
open BrownianSharp.AlignmentPaperFractionalSheetSameSpaceSlice
open BrownianSharp.AlignmentGaussianActualFractionalUpperLog
open BrownianSharp.Latest
open HaarQuarter

/-- The isotropic MvN feature ball inherits the scalar-preimage entropy lower
bound through the actual scaled fractional integration image. -/
theorem commonH_fractionalSheetFeature_entropy_lower_of_scalar
    {ν : ℕ} (h : ℝ) (hh : 0 < h ∧ h < 1) (hν : 2 ≤ ν)
    (hscalar : ScalarPreimages) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-(h+1/2)) *
        (Real.log (k:ℝ))^((h+1/2)*((ν-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureBall (fractionalSheetFeature (fun _ : Fin ν => h)
            (fun _ => hh))) := by
  classical
  let H : Fin ν → ℝ := fun _ => h
  let hH : ∀ i, 0 < H i ∧ H i < 1 := fun _ => hh
  let a : Fin ν → ℝ := fun _ => h+1/2
  let r : ℝ := h+1/2
  have hr : 1/2 < r := by dsimp [r]; linarith
  have ha : ∀ i, 1/2 < a i := by intro i; dsimp [a]; linarith
  obtain ⟨c₀,hc₀,k₀,hk₀,hEntropy⟩ :=
    AlignmentPaperFractionalEntropyRoute.entropy_lower_of_scalar hν hr hscalar
  let C : ℝ := ∏ i : Fin ν, Real.Gamma (H i+1/2) *
    ‖mvNFullFeature (H i-1/2) 1
      (mvNFullKernel_memLp (hH i).1 (hH i).2
        (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i hi
    apply mul_pos
    · exact Real.Gamma_pos_of_pos (by linarith [(hH i).1])
    · apply inv_pos.mpr
      exact mvNFullKernel_one_norm_pos (H i-1/2)
        (mvNFullKernel_memLp (hH i).1 (hH i).2
          (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))
  refine ⟨C*c₀,mul_pos hC hc₀,k₀,hk₀,?_⟩
  intro k hk
  let J := Latest.fractionalIntegrationBall a
  let K := featureBall (fractionalSheetFeature H hH)
  have hJ : ENNReal.ofReal (c₀*(k:ℝ)^(-r) *
      (Real.log (k:ℝ))^(r*((ν-1:ℕ):ℝ)+1/2)) ≤
      HaarQuarter.TheoremD.entropyNumber k J := by
    simpa [J,a,r,mul_assoc] using hEntropy k hk
  have hT : ‖(ContinuousLinearMap.id ℝ
      (C(BrownianCubeAnchor ν,ℝ)))‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_id]
  have hsub : (fun f : C(BrownianCubeAnchor ν,ℝ) => C • f) '' J ⊆
      (ContinuousLinearMap.id ℝ (C(BrownianCubeAnchor ν,ℝ))) '' K := by
    intro f hf
    rcases hf with ⟨f₀,hf₀,rfl⟩
    have hfactor := scaled_fractionalIntegrationBall_subset_sheetFeatureBall H hH
    have hK : C • f₀ ∈ K := hfactor ⟨f₀,hf₀,rfl⟩
    exact ⟨C • f₀,hK,by simp⟩
  have htrans := entropyNumber_ge_of_scaled_contractive_image
    (ContinuousLinearMap.id ℝ (C(BrownianCubeAnchor ν,ℝ))) hT K J C
    (c₀*(k:ℝ)^(-r)*(Real.log (k:ℝ))^(r*((ν-1:ℕ):ℝ)+1/2)) hC
    (by positivity) hsub k hJ
  simpa [C,H,hH,r,mul_assoc] using htrans

/-- Isotropic actual-sheet logarithmic lower bound supplied by scalar atom
preimages. The only sample-dependent premise is positivity of the actual
small-ball probability, needed to take its real logarithm. -/
theorem commonH_fractionalSheet_lowerLog_of_scalar
    {ν : ℕ} (h : ℝ) (hh : 0 < h ∧ h < 1) (hν : 2 ≤ ν)
    (hscalar : ScalarPreimages) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube ν Ω P), B.H = (fun _ => h) →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} →
          c * Latest.smallBallRate (h⁻¹)
            (((ν-1:ℕ):ℝ) + (ν:ℝ)/(2*h)) ε ≤
            -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  classical
  let H : Fin ν → ℝ := fun _ => h
  let hH : ∀ i, 0 < H i ∧ H i < 1 := fun _ => hh
  let r : ℝ := h+1/2
  let b : ℝ := r*((ν-1:ℕ):ℝ)+1/2
  have hr : 1/2 < r := by dsimp [r]; linarith
  have hb : 0 ≤ b := by dsimp [b,r]; positivity
  obtain ⟨cE,hcE,k₀,hk₀,hE⟩ :=
    commonH_fractionalSheetFeature_entropy_lower_of_scalar h hh hν hscalar
  have hEntropy : ∃ c : ℝ, 0 < c ∧ ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r b k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureBall (fractionalSheetFeature H hH)) := by
    refine ⟨cE,hcE,k₀,?_⟩
    intro k hk
    have hh' := hE k hk
    simpa [logarithmicIndexRate,r,b,H,hH,mul_assoc] using hh'
  obtain ⟨c,ε₀,hc,hε₀,hε₀small,hUpper⟩ :=
    uniform_smallBall_probability_upper_of_entropy_lower
      (featureBall (fractionalSheetFeature H hH)) r b hr hb hEntropy
  refine ⟨c,ε₀,hc,hε₀,hε₀small,?_⟩
  intro Ω _ P _ B hBH ε hε hsmall hpositive
  let μ : Measure C(BrownianCubeAnchor ν,ℝ) := fractionalSheetLaw B
  have hμ : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (P.map B.path)
    refine ⟨?_⟩
    rw [Measure.map_apply B.measurable_path MeasurableSet.univ]
    simp
  have hmass : μ.real (Metric.closedBall 0 ε) =
      P.real {ω | ‖B.path ω‖ ≤ ε} := by
    change (P.map B.path).real (Metric.closedBall 0 ε) = _
    rw [Measure.real_def,
      Measure.map_apply B.measurable_path measurableSet_closedBall,
      Measure.real_def]
    congr 1
  have hshift : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ x ∈ featureBall (fractionalSheetFeature H hH),
        ENNReal.ofReal (Real.exp (-(R^2)/2)) * μ (Metric.closedBall 0 η) ≤
          μ (Metric.closedBall (R • x) η) := by
    intro R hR η hη x hx
    exact fractionalSheetLaw_ball_shift_lower B H hH hBH R η hR hη x hx
  have hprob := hUpper μ hμ hshift ε hε hsmall
  have hpow : (r-1/2)⁻¹ = h⁻¹ := by dsimp [r]; ring
  have hcast : ((ν-1:ℕ):ℝ) = (ν:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ν)]
    norm_num
  have hlogpow : b/(r-1/2) = ((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h) := by
    dsimp [b,r]
    rw [hcast]
    field_simp [ne_of_gt hh.1]
    <;> ring
  have hposμ : 0 < μ.real (Metric.closedBall 0 ε) := by
    rw [hmass]
    exact hpositive
  have hlog := Real.log_le_log hposμ (by simpa [hmass] using hprob)
  rw [Real.log_exp] at hlog
  have hpow' : (r-2⁻¹)⁻¹ = h⁻¹ := by simpa using hpow
  have hlogpow' : b/(r-2⁻¹) = ((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h) := by
    simpa using hlogpow
  rw [hpow',hlogpow'] at hlog
  rw [hmass] at hlog
  linarith

/-- Transfer the isotropic lower logarithmic bound to an arbitrary actual
fractional sheet by restricting its path to the minimum-Hurst coordinates. -/
theorem fractionalSheet_lowerLog_of_scalar
    {d ν : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (hν : 2 ≤ ν)
    (hm : Latest.minimumMultiplicity H h ν)
    (hscalar : ScalarPreimages) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P), B.H = H →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} →
          c * Latest.smallBallRate (h⁻¹)
            (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε ≤
            -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  have hh : 0 < h ∧ h < 1 := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by rw [hm.2]; omega)
    have heq : H i = h := (Finset.mem_filter.mp hi).2
    rw [← heq]
    exact ⟨(hH i).1,(hH i).2⟩
  obtain ⟨c,ε₀,hc,hε₀,hε₀small,hLower⟩ :=
    commonH_fractionalSheet_lowerLog_of_scalar h hh hν hscalar
  refine ⟨c,ε₀,hc,hε₀,hε₀small,?_⟩
  intro Ω _ P _ B hBH ε hε hsmall hpositive
  have hmB : Latest.minimumMultiplicity B.H h ν := by
    simpa [hBH] using hm
  obtain ⟨j,hactive,Bν,hBνH,hpath,hnorm,hprob⟩ :=
    exists_sameSpace_minimumMultiplicity_slice B h hmB (by omega)
  have hpositiveν : 0 < P.real {ω | ‖Bν.path ω‖ ≤ ε} := by
    exact lt_of_lt_of_le hpositive (hprob ε)
  have hlower := hLower Ω P Bν hBνH ε hε hsmall hpositiveν
  have hlog := Real.log_le_log hpositive (hprob ε)
  linarith

/-- The fractional sheet statement with its entropy-lower input explicit.
The MvN upper logarithm remains independent and is combined here with the
scalar-preimage lower route and same-space minimum-coordinate restriction. -/
theorem latest_fractionalSheet_of_scalar :
    ∀ d : ℕ, 2 ≤ d → ∀ H : Fin d → ℝ,
      (∀ i, 0 < H i ∧ H i < 1) → ∀ h : ℝ, ∀ ν : ℕ, 2 ≤ ν →
      Latest.minimumMultiplicity H h ν → ScalarPreimages →
      ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
        ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P]
          (B : FractionalBrownianSheetOnCube d Ω P), B.H = H →
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
            c*Latest.smallBallRate h⁻¹
              (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε ≤
                -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ∧
            -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ≤
              C*Latest.smallBallRate h⁻¹
                (((ν-1:ℕ):ℝ)+(ν:ℝ)/(2*h)) ε := by
  intro d hd H hH h ν hν hmin hscalar
  obtain ⟨cU,εU,hcU,hεU,hεUsmall,hUpper⟩ :=
    fractionalSheet_upperLog_of_actualMvN_scalar_filtrations_any_dimension
      hd H hH h ν hν hmin
  obtain ⟨cL,εL,hcL,hεL,hεLsmall,hLower⟩ :=
    fractionalSheet_lowerLog_of_scalar hd H hH h hν hmin hscalar
  let ε₀ := min εU εL
  refine ⟨cL,cU,ε₀,hcL,hcU,lt_min hεU hεL,?_,?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) hεLsmall
  · intro Ω _ P _ B hBH ε hε hsmall
    have hsmallU : ε ≤ εU := le_trans hsmall (min_le_left _ _)
    have hsmallL : ε ≤ εL := le_trans hsmall (min_le_right _ _)
    have hu := hUpper Ω P B hBH ε hε hsmallU
    have hl := hLower Ω P B hBH ε hε hsmallL hu.1
    exact ⟨hl,hu.2⟩

end BrownianSharp.AlignmentPaperFractionalSheetScalarLower
