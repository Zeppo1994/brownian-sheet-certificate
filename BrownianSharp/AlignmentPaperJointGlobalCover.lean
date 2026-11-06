import BrownianSharp.AlignmentPaperJointDyadicStages
import BrownianSharp.AlignmentPaperJointDyadicSums
import BrownianSharp.Carl
import BrownianSharp.EntropyCoverInversion

/-! Generic finite-grade covering assembly for the actual common-grid feature
coordinates.  The target-side decoder is the existing DVP reconstruction. -/

noncomputable section
open scoped BigOperators ENNReal NNReal
set_option maxHeartbeats 500000

namespace BrownianSharp.AlignmentPaperJointGlobalCover

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointDyadicSums
open BrownianSharp.AlignmentPaperJointDyadicBitBudget
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperLpDvpBlockCover
open BrownianSharp.AlignmentPaperLpDvpReconstruction
open BrownianSharp.Torus
open BrownianSharp.AlignmentPaperJointDictionary

theorem exists_finite_cover_of_entropyNumber_lt
    {X : Type*} [PseudoEMetricSpace X] (K : Set X) (k : ℕ) (ρ : ℝ≥0)
    (hent : HaarQuarter.TheoremD.entropyNumber k K < (ρ : ℝ≥0∞)) :
    ∃ C : Set X, C.Finite ∧ Metric.IsCover (2 * ρ) K C ∧
      C.encard ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  have hext := externalCover_le_of_entropyNumber_lt k K ρ hent
  have hcovering : Metric.coveringNumber (2 * ρ) K ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞) :=
    (Metric.coveringNumber_two_mul_le_externalCoveringNumber ρ K).trans hext
  have htop : Metric.coveringNumber (2 * ρ) K ≠ ⊤ := by
    intro htop
    rw [htop] at hcovering
    simp at hcovering
  obtain ⟨C, hCK, hCfin, hCcover, hCcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber htop
  exact ⟨C, hCfin, hCcover, by rw [hCcard]; exact hcovering⟩

theorem exists_finite_lipschitz_image_cover
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (T : X → Y) (L : ℝ≥0) (hT : LipschitzWith L T)
    (K : Set X) (k : ℕ) (ρ : ℝ≥0)
    (hent : HaarQuarter.TheoremD.entropyNumber k K < (ρ : ℝ≥0∞)) :
    ∃ C : Set Y, C.Finite ∧ Metric.IsCover (L * (2 * ρ)) (T '' K) C ∧
      C.encard ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  obtain ⟨A, hAfin, hAcover, hAcard⟩ := exists_finite_cover_of_entropyNumber_lt K k ρ hent
  refine ⟨T '' A, hAfin.image T, ?_, ?_⟩
  · exact hAcover.image_lipschitz hT
  · exact (Set.encard_image_le T A).trans hAcard

/-- The finite grade covers are assembled by the actual pointwise grade
decomposition. The list condition states that every grade contribution and
the terminal remainder lie in the corresponding covered source sets. -/
theorem entropyNumber_le_of_grade_list_decomposition
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (pieces : List (Carl.CoverPiece X)) (k : ℕ)
    (hdecomp : ∀ x ∈ K, ∃ xs : List X,
      xs.sum = x ∧ List.Forall₂ (fun z p => z ∈ p.source) xs pieces)
    (hbudget : (pieces.map (fun p => p.centers.encard)).prod ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ Carl.sumRadii pieces := by
  apply Carl.entropyNumber_le_sumRadii_of_multiscale_budget K pieces k ?_ hbudget
  intro x hx
  obtain ⟨xs, hsum, hrel⟩ := hdecomp x hx
  rw [Carl.sumSources_eq_sumSetList]
  rw [← hsum]
  exact Carl.list_sum_mem_sumSources xs (pieces.map Carl.CoverPiece.source)
    ((List.forall₂_map_right_iff).2 hrel)

theorem forall₂_ofFn {α β : Type*} (n : ℕ) (f : Fin n → α) (g : Fin n → β)
    (R : α → β → Prop) (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      apply List.Forall₂.cons
      · exact h 0
      · apply ih
        intro i
        exact h i.succ

noncomputable def indexedGradeCoverPieces
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {N : ℕ} (G C : Fin N → Set X) (r : Fin N → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i) (G i) (C i))
    (hfinite : ∀ i, (C i).Finite) : List (Carl.CoverPiece X) :=
  List.ofFn fun i => ⟨G i, C i, r i, hcover i, hfinite i⟩

theorem indexedGradeCoverPieces_forall₂
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {N : ℕ} (G C : Fin N → Set X) (r : Fin N → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i) (G i) (C i))
    (hfinite : ∀ i, (C i).Finite) (v : Fin N → X)
    (hmem : ∀ i, v i ∈ G i) :
    List.Forall₂ (fun z p => z ∈ p.source) (List.ofFn v)
      (indexedGradeCoverPieces G C r hcover hfinite) := by
  apply forall₂_ofFn
  intro i
  exact hmem i

theorem entropyNumber_le_of_finite_grade_window
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) {N : ℕ} (G C : Fin N → Set X) (r : Fin N → ℝ≥0)
    (hcover : ∀ i, Metric.IsCover (r i) (G i) (C i))
    (hfinite : ∀ i, (C i).Finite)
    (tail : Carl.CoverPiece X) (k : ℕ)
    (hbudget : (((indexedGradeCoverPieces G C r hcover hfinite ++ [tail]).map
      (fun p => p.centers.encard)).prod) ≤ ((2^(k-1):ℕ):ℕ∞))
    (hdecomp : ∀ x ∈ K, ∃ v : Fin N → X, ∃ t : X,
      (∀ i, v i ∈ G i) ∧ t ∈ tail.source ∧ (List.ofFn v).sum + t = x) :
    HaarQuarter.TheoremD.entropyNumber k K ≤
      Carl.sumRadii (indexedGradeCoverPieces G C r hcover hfinite ++ [tail]) := by
  apply entropyNumber_le_of_grade_list_decomposition K _ k ?_ hbudget
  intro x hx
  obtain ⟨v, t, hv, ht, hsum⟩ := hdecomp x hx
  refine ⟨List.ofFn v ++ [t], ?_, ?_⟩
  · simpa only [List.sum_append, List.sum_singleton] using hsum
  · exact List.rel_append
      (indexedGradeCoverPieces_forall₂ G C r hcover hfinite v hv)
      (List.Forall₂.cons ht List.Forall₂.nil)

def commonGridDecoder {d n : ℕ} :
    PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) →L[ℝ]
      C(UnitAddTorus (Fin d), ℂ) :=
  (oversampledDvpRealCoordinateReconstruction
      (gradeCommonBandwidth (d := d) (n := n))
      (by intro i; dsimp [gradeCommonBandwidth]; positivity)).comp
    (PiLp.equivₗᵢ (𝕜 := ℝ) (fun _ : Fin (DictionaryDimension d n) => ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem commonGridDecoder_norm_le {d n : ℕ} :
    ‖commonGridDecoder (d := d) (n := n)‖ ≤ 2 * (5 : ℝ) ^ d := by
  let N := gradeCommonBandwidth (d := d) (n := n)
  have hN : ∀ i, 0 < N i := by intro i; dsimp [N, gradeCommonBandwidth]; positivity
  have hrec : ‖oversampledDvpReconstructionCLM N hN‖ ≤ (5 : ℝ) ^ d := by
    change ‖(oversampledDvpReconstructionLinearMap N).mkContinuous
      ((5 : ℝ)^d) (oversampledDvpReconstruction_norm_le N hN)‖ ≤ _
    exact LinearMap.mkContinuous_norm_le _ (by positivity) (oversampledDvpReconstruction_norm_le N hN)
  have hdec : ‖decodeRealSamplesCLM N‖ ≤ 2 := by
    unfold decodeRealSamplesCLM
    exact LinearMap.mkContinuous_norm_le _ (by norm_num) _
  have hreal : ‖oversampledDvpRealCoordinateReconstruction N hN‖ ≤
      (5 : ℝ) ^ d * 2 := by
    unfold oversampledDvpRealCoordinateReconstruction
    calc
      _ ≤ ‖ContinuousLinearMap.restrictScalars ℝ
            (oversampledDvpReconstructionCLM N hN)‖ *
          ‖decodeRealSamplesCLM N‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖oversampledDvpReconstructionCLM N hN‖ *
          ‖decodeRealSamplesCLM N‖ := by rw [ContinuousLinearMap.norm_restrictScalars]
      _ ≤ (5 : ℝ)^d * 2 := mul_le_mul hrec hdec (norm_nonneg _) (by norm_num)
  have hequiv : ‖(PiLp.equivₗᵢ (𝕜 := ℝ) (fun _ : Fin (DictionaryDimension d n) => ℝ)).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖PiLp.equivₗᵢ (𝕜 := ℝ)
      (fun _ : Fin (DictionaryDimension d n) => ℝ) x‖ ≤ 1 * ‖x‖
    simpa using (PiLp.equivₗᵢ (𝕜 := ℝ)
      (fun _ : Fin (DictionaryDimension d n) => ℝ)).norm_map x
  calc
    ‖commonGridDecoder (d := d) (n := n)‖ ≤
        ‖oversampledDvpRealCoordinateReconstruction N hN‖ *
          ‖(PiLp.equivₗᵢ (𝕜 := ℝ) (fun _ : Fin (DictionaryDimension d n) => ℝ) :
            PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) ≃ₗᵢ[ℝ]
              (Fin (DictionaryDimension d n) → ℝ)).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((5 : ℝ) ^ d * 2) * 1 := by
      exact mul_le_mul hreal hequiv (norm_nonneg _) (by norm_num)
    _ = 2 * (5 : ℝ) ^ d := by ring

theorem commonGridDecoder_lipschitz {d n : ℕ} :
    LipschitzWith ⟨2 * (5 : ℝ) ^ d, by positivity⟩
      (commonGridDecoder (d := d) (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖commonGridDecoder (d := d) (n := n) x -
      commonGridDecoder (d := d) (n := n) y‖ ≤
    (2 * (5 : ℝ) ^ d) * ‖x - y‖
  rw [← map_sub]
  calc
    ‖commonGridDecoder (d := d) (n := n) (x - y)‖ ≤
        ‖commonGridDecoder (d := d) (n := n)‖ * ‖x - y‖ :=
      (commonGridDecoder (d := d) (n := n)).le_opNorm _
    _ ≤ (2 * (5 : ℝ) ^ d) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (commonGridDecoder_norm_le (d := d) (n := n))
        (norm_nonneg _)

def commonGridEncodedVector {d n : ℕ}
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) :=
  WithLp.toLp ∞ (encodeComplexSamples (gradeCommonBandwidth (d := d) (n := n)) f)

def gradeSampleCoordinates {d n : ℕ} (a : GradeSamples d n) :
    Fin (JointSampleDimension d n) → ℝ :=
  fun i => a ((jointSampleIndexEquivFin d n).symm i)

def gradeSampleVector {d n : ℕ} (a : GradeSamples d n) :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) :=
  WithLp.toLp 2 (gradeSampleCoordinates (d := d) (n := n) a)

theorem featureMap_gradeSampleVector_encodeSmoothGradeSamples {d n : ℕ}
    (g : RealPeriodic d) :
    featureMap (d := d) (n := n)
      (gradeSampleVector (d := d) (n := n)
        (encodeSmoothGradeSamples (d := d) (n := n) g)) =
      commonGridEncodedVector (d := d) (n := n)
        (smoothGradePolynomial (d := d) (n := n) g) := by
  have hsyn : jointGradeSynthesisCLM (d := d) (n := n)
      (gradeSampleVector (d := d) (n := n)
        (encodeSmoothGradeSamples (d := d) (n := n) g)) =
      smoothGradePolynomial (d := d) (n := n) g := by
    change jointGradeSynthesisCLM (d := d) (n := n)
      (WithLp.toLp 2 (fun i : Fin (JointSampleDimension d n) =>
        encodeSmoothGradeSamples (d := d) (n := n) g
          ((jointSampleIndexEquivFin d n).symm i))) = _
    rw [jointGradeSynthesisCLM_apply_decode]
    exact gradeDvpReconstruction_encode_exact g
  change jointGradeSynthesisCLM (WithLp.toLp 2
    (gradeSampleCoordinates (d := d) (n := n)
      (encodeSmoothGradeSamples (d := d) (n := n) g))) =
    smoothGradePolynomial (d := d) (n := n) g at hsyn
  ext i
  simp [featureMap_apply, commonGridEncodedVector, gradeSampleVector, gradeSampleCoordinates,
    jointGradeCommonGridFeatureCLM_apply, hsyn, encodeComplexSamples, outputEquivFin,
    gridRealIndexEquiv]

theorem commonGridDecoder_featureMap_gradeSampleVector_encodeSmoothGradeSamples
    {d n : ℕ} (g : RealPeriodic d) :
    commonGridDecoder (d := d) (n := n)
      (featureMap (d := d) (n := n)
        (gradeSampleVector (d := d) (n := n)
          (encodeSmoothGradeSamples (d := d) (n := n) g))) =
      smoothGradePolynomial (d := d) (n := n) g := by
  rw [featureMap_gradeSampleVector_encodeSmoothGradeSamples]
  exact commonDvpReconstruction_smoothGrade_exact g

def decodedJointLpFeatureImage {d n : ℕ} (p B : ℝ) :
    Set C(UnitAddTorus (Fin d), ℂ) :=
  commonGridDecoder (d := d) (n := n) ''
    jointLpFeatureImage (d := d) (n := n) p B

def gradeSeriesSourceRadius (d : ℕ) (p A : ℝ) (n : ℕ) : ℝ :=
  A * (2 : ℝ) ^ (-(1 - 1 / p) * (n : ℝ)) *
    (n + 1 : ℝ) ^ ((d - 1 : ℕ) * (1 / p - 1 / 2))

def GradeSeriesClass (d : ℕ) (p A : ℝ) :
    Set C(UnitAddTorus (Fin d), ℂ) :=
  {f | ∃ u : ℕ → C(UnitAddTorus (Fin d), ℂ),
    (∀ n, u n ∈ decodedJointLpFeatureImage (d := d) (n := n) p
      (gradeSeriesSourceRadius d p A n)) ∧ f = ∑' n, u n}

theorem decodedJointLpFeatureImage_norm_le
    {d n : ℕ} {p B : ℝ} (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    {f : C(UnitAddTorus (Fin d), ℂ)}
    (hf : f ∈ decodedJointLpFeatureImage (d := d) (n := n) p B) :
    ‖f‖ ≤ (2 * (5 : ℝ)^d) * jointRowBound d n * B := by
  rcases hf with ⟨z, ⟨x, hx, hfeature⟩, rfl⟩
  have hsource : ‖WithLp.toLp 2 x‖ ≤ B :=
    lpBudget_euclidean_norm_le (by linarith) (by linarith) hB x hx
  have hD : 0 < DictionaryDimension d n := dictionaryDimension_pos d n
  have hrow : 0 ≤ jointRowBound d n := by unfold jointRowBound; positivity
  have hfeatureNorm : ‖z‖ ≤ jointRowBound d n * B := by
    rw [← hfeature]
    exact (featureMap_norm_le hD (WithLp.toLp 2 x)).trans
      (mul_le_mul_of_nonneg_left hsource hrow)
  calc
    ‖commonGridDecoder (d := d) (n := n) z‖ ≤
        ‖commonGridDecoder (d := d) (n := n)‖ * ‖z‖ :=
      (commonGridDecoder (d := d) (n := n)).le_opNorm z
    _ ≤ (2 * (5 : ℝ)^d) * (jointRowBound d n * B) := by
      exact mul_le_mul (commonGridDecoder_norm_le (d := d) (n := n)) hfeatureNorm
        (norm_nonneg _) (by positivity)
    _ = (2 * (5 : ℝ)^d) * jointRowBound d n * B := by ring

theorem jointRowBound_le_polynomial {d n : ℕ} (hd : 2 ≤ d) :
    jointRowBound d n ≤
      (Real.sqrt ((25 / 4 : ℝ)^d) + 1) *
      (n + 1 : ℝ) ^ ((d - 1 : ℝ) / 2) := by
  let q := d - 1
  let m := (n + 1 : ℝ)
  let c := (25 / 4 : ℝ)^d
  have hd0 : 0 < d := by omega
  have hq : 0 < q := by dsimp [q]; omega
  have hm : 1 ≤ m := by dsimp [m]; norm_num
  have hcountR :
      (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) ≤ m ^ q := by
    have hshape : Fintype.card (Shape d n) =
        ((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card := by
      simp [Shape]
    rw [← hshape, shape_card d n hd0]
    have h := hyperbolicCount_upper_shift (by omega : 1 ≤ d) n
    simpa [m, q, hyperbolicCount] using h
  have hqpow : Real.sqrt (m ^ q) = m ^ ((q : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ m)]
    congr 1
    ring
  have hcountRoot :
      Real.sqrt (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) ≤
        m ^ ((q : ℝ) / 2) := by
    calc
      _ ≤ Real.sqrt (m ^ q) := Real.sqrt_le_sqrt hcountR
      _ = _ := hqpow
  have hqhalf : 0 ≤ ((q : ℝ) / 2) := by positivity
  have hmhalf : 1 ≤ m ^ ((q : ℝ) / 2) := Real.one_le_rpow hm hqhalf
  have hrow :
      Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) * c) + 1 ≤
        (Real.sqrt c + 1) * m ^ ((q : ℝ) / 2) := by
    have hc : 0 ≤ c := by positivity
    calc
      Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) * c) + 1 =
          Real.sqrt (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) * Real.sqrt c + 1 := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _)]
      _ ≤ m ^ ((q : ℝ) / 2) * Real.sqrt c + 1 := by
            gcongr
      _ ≤ m ^ ((q : ℝ) / 2) * Real.sqrt c +
          m ^ ((q : ℝ) / 2) := by linarith
      _ = (Real.sqrt c + 1) * m ^ ((q : ℝ) / 2) := by ring
  simpa [jointRowBound, q, m, c, Nat.cast_sub (by omega : 1 ≤ d)] using hrow

def gradeSeriesNormEnvelope (d : ℕ) (p A : ℝ) (n : ℕ) : ℝ :=
  (2 * (5 : ℝ)^d) * (Real.sqrt ((25 / 4 : ℝ)^d) + 1) * A *
    (2 : ℝ) ^ (-(1 - 1 / p) * (n : ℝ)) *
    (n + 1 : ℝ) ^ ((d - 1 : ℝ) / p)

theorem gradeSeriesComponent_norm_le
    {d n : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) {f : C(UnitAddTorus (Fin d), ℂ)}
    (hf : f ∈ decodedJointLpFeatureImage (d := d) (n := n) p
      (gradeSeriesSourceRadius d p A n)) :
    ‖f‖ ≤ gradeSeriesNormEnvelope d p A n := by
  have hp0 : 0 < p := by linarith
  have hB : 0 < gradeSeriesSourceRadius d p A n := by
    unfold gradeSeriesSourceRadius
    positivity
  have hbase := decodedJointLpFeatureImage_norm_le hp hp2 hB hf
  have hrow := jointRowBound_le_polynomial (d := d) (n := n) hd
  have hrow0 : 0 ≤ jointRowBound d n := by unfold jointRowBound; positivity
  have hmult := mul_le_mul_of_nonneg_right hrow (le_of_lt hB)
  have hrowB : jointRowBound d n * gradeSeriesSourceRadius d p A n ≤
      (Real.sqrt ((25 / 4 : ℝ)^d) + 1) *
        ((n + 1 : ℝ) ^ ((d - 1 : ℝ)/2) *
          gradeSeriesSourceRadius d p A n) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hrow hB.le
  have hpow :
      (n + 1 : ℝ) ^ ((d - 1 : ℝ)/2) *
        (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 / p - 1 / 2)) =
      (n + 1 : ℝ) ^ ((d - 1 : ℝ)/p) := by
    rw [← Real.rpow_add (by positivity : 0 < (n + 1 : ℝ))]
    congr 1
    ring
  calc
    ‖f‖ ≤ (2 * (5 : ℝ)^d) * jointRowBound d n *
        gradeSeriesSourceRadius d p A n := hbase
    _ ≤ (2 * (5 : ℝ)^d) *
        ((Real.sqrt ((25 / 4 : ℝ)^d) + 1) *
          ((n + 1 : ℝ) ^ ((d - 1 : ℝ)/2) *
            gradeSeriesSourceRadius d p A n)) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hrowB (show 0 ≤ 2 * (5 : ℝ)^d by positivity)
    _ = gradeSeriesNormEnvelope d p A n := by
      unfold gradeSeriesNormEnvelope gradeSeriesSourceRadius
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      simp only [Nat.cast_one]
      calc
        _ = 2 * (5 : ℝ)^d * (Real.sqrt ((25 / 4 : ℝ)^d) + 1) *
            (A * (2 : ℝ) ^ (-(1 - 1 / p) * (n : ℝ)) *
              ((n + 1 : ℝ) ^ ((d - 1 : ℝ)/2) *
                (n + 1 : ℝ) ^ ((d - 1 : ℝ) * (1 / p - 1 / 2)))) := by ring
        _ = 2 * (5 : ℝ)^d * (Real.sqrt ((25 / 4 : ℝ)^d) + 1) *
            A * (2 : ℝ) ^ (-(1 - 1 / p) * (n : ℝ)) *
              (n + 1 : ℝ) ^ ((d - 1 : ℝ)/p) := by
          rw [hpow]
          ring

theorem exists_decodedJointLpFeatureImage_cover_of_entropy_bound
    {d n k : ℕ} {p B R : ℝ} {ρ : ℝ≥0} (hR : 0 ≤ R)
    (hRρ : R < (ρ : ℝ))
    (hent : HaarQuarter.TheoremD.entropyNumber k
      (jointLpFeatureImage (d := d) (n := n) p B) ≤ ENNReal.ofReal R) :
    ∃ C : Set C(UnitAddTorus (Fin d), ℂ), C.Finite ∧
      Metric.IsCover (⟨2 * (5 : ℝ) ^ d, by positivity⟩ * (2 * ρ))
        (decodedJointLpFeatureImage (d := d) (n := n) p B) C ∧
      C.encard ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  have hstrict : HaarQuarter.TheoremD.entropyNumber k
      (jointLpFeatureImage (d := d) (n := n) p B) < (ρ : ℝ≥0∞) := by
    exact hent.trans_lt
      ((ENNReal.ofReal_lt_coe_iff hR).2 hRρ)
  simpa only [decodedJointLpFeatureImage] using
    exists_finite_lipschitz_image_cover
      (commonGridDecoder (d := d) (n := n))
      ⟨2 * (5 : ℝ) ^ d, by positivity⟩
      (commonGridDecoder_lipschitz (d := d) (n := n))
      (jointLpFeatureImage (d := d) (n := n) p B) k ρ hstrict

theorem exists_decodedJointLpFeatureImage_dyadic_cover
    {d n J : ℕ} {p B : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hB : 0 < B)
    (hJD : 2^J ≤ JointSampleDimension d n) :
    ∃ C : Set C(UnitAddTorus (Fin d), ℂ), C.Finite ∧
      Metric.IsCover
        (⟨2 * (5 : ℝ)^d, by positivity⟩ *
          (2 * Real.toNNReal (2 * (3 * stageScale d n B * ((2:ℝ)^J)^(-1/p)))))
        (decodedJointLpFeatureImage (d := d) (n := n) p B) C ∧
      C.encard ≤ ((2 ^ (Nat.ceil ((6*codingConstant+1)*(2:ℝ)^J*
        logRatio (JointSampleDimension d n) J) - 1) : ℕ) : ℕ∞) := by
  let R := 3 * stageScale d n B * ((2:ℝ)^J)^(-1/p)
  have hs := stageScale_pos (d := d) (n := n) hB
  have hp0 : 0 < p := by linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hEntropy := jointFeature_dyadic_entropy_budgeted hp hp2 hB hJD
  have hRρ : R < (Real.toNNReal (2 * R) : ℝ) := by
    rw [Real.coe_toNNReal']
    rw [max_eq_left (show 0 ≤ 2 * R by positivity)]
    nlinarith [hR]
  simpa only [R] using
    exists_decodedJointLpFeatureImage_cover_of_entropy_bound
      (R := R) (ρ := Real.toNNReal (2 * R)) hR.le hRρ
      hEntropy

noncomputable def decodedGradeDyadicRadius (d n : ℕ) (p B : ℝ) (J : ℕ) : ℝ≥0 :=
  ⟨2 * (5 : ℝ)^d, by positivity⟩ *
    (2 * Real.toNNReal (2 * (3 * stageScale d n B * ((2:ℝ)^J)^(-1/p))))

def decodedGradeDyadicBudget (d n J : ℕ) : ℕ∞ :=
  ((2 ^ (Nat.ceil ((6*codingConstant+1)*(2:ℝ)^J*
    logRatio (JointSampleDimension d n) J) - 1) : ℕ) : ℕ∞)

theorem smoothGrade_mem_decodedJointLpFeatureImage
    {d n : ℕ} {p B : ℝ} (g : RealPeriodic d)
    (hbudget : (∑ i : Fin (JointSampleDimension d n),
      |gradeSampleCoordinates (d := d) (n := n) (encodeSmoothGradeSamples g) i| ^ p) ≤ B ^ p) :
    smoothGradePolynomial (d := d) (n := n) g ∈
      decodedJointLpFeatureImage (d := d) (n := n) p B := by
  refine ⟨featureMap (d := d) (n := n)
    (gradeSampleVector (d := d) (n := n) (encodeSmoothGradeSamples g)), ?_, ?_⟩
  · exact ⟨gradeSampleCoordinates (d := d) (n := n) (encodeSmoothGradeSamples g),
      hbudget, rfl⟩
  · exact commonGridDecoder_featureMap_gradeSampleVector_encodeSmoothGradeSamples g

end BrownianSharp.AlignmentPaperJointGlobalCover
