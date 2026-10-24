import BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
import BrownianSharp.AlignmentPeriodicL1Fourier
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentPeriodicCutoffPartition

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicL1AdmissibleEntropyBoundary
open BrownianSharp.AlignmentPeriodicL1Fourier
open BrownianSharp.AlignmentPeriodicFourierReconstruction
open BrownianSharp.AlignmentPeriodicCutoffPartition
open BrownianSharp.AlignmentPeriodicReconstruction
open BrownianSharp.AtomicBlockKernelL2
open UnitAddTorus

private def ambientVolume (d : ℕ) : Measure (UnitAddTorus (Fin d)) := volume

local instance : MeasureSpace UnitAddCircle :=
  BrownianSharp.AlignmentPeriodicL1Fourier.instMeasureSpaceUnitAddCircle_brownianSharp
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance (d : ℕ) : Measure.IsAddHaarMeasure
    (volume : Measure (UnitAddTorus (Fin d))) := by
  change Measure.IsAddHaarMeasure
    (Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  infer_instance

local instance (d : ℕ) : IsProbabilityMeasure (sourceMeasure d) := by
  dsimp [sourceMeasure]
  infer_instance

private theorem sourceMeasure_eq_volume (d : ℕ) : sourceMeasure d =
    (volume : Measure (UnitAddTorus (Fin d))) := by
  change Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) =
    (volume : Measure (UnitAddTorus (Fin d)))
  rw [show (volume : Measure (UnitAddTorus (Fin d))) =
    Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) by rfl]
  rfl

private theorem ae_local_to_source {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[volume] g) : f =ᵐ[sourceMeasure d] g := by
  simpa [sourceMeasure_eq_volume d] using h

private theorem ae_source_to_local {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[sourceMeasure d] g) : f =ᵐ[volume] g := by
  simpa [sourceMeasure_eq_volume d] using h

private theorem ae_ambient_to_source {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[ambientVolume d] g) : f =ᵐ[sourceMeasure d] g := by
  letI : MeasureSpace UnitAddCircle := AddCircle.measureSpace 1
  have hμ : sourceMeasure d = ambientVolume d := by
    dsimp [sourceMeasure]
    exact (BrownianSharp.unitAddTorus_volume_eq_productHaar d).symm
  simpa [ambientVolume, hμ] using h

private theorem ae_source_to_ambient {d : ℕ} {f g : UnitAddTorus (Fin d) → ℝ}
    (h : f =ᵐ[sourceMeasure d] g) : f =ᵐ[ambientVolume d] g := by
  letI : MeasureSpace UnitAddCircle := AddCircle.measureSpace 1
  have hμ : sourceMeasure d = ambientVolume d := by
    dsimp [sourceMeasure]
    exact (BrownianSharp.unitAddTorus_volume_eq_productHaar d).symm
  simpa [ambientVolume, hμ] using h

private theorem l1CutoffBlock_toLp_norm_eq_volume {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (f : UnitAddTorus (Fin d) → ℝ) :
    ‖(l1CutoffBlock φ s f).toLp 2 (sourceMeasure d) ℂ‖ =
      ‖(l1CutoffBlock φ s f).toLp 2
        (volume : Measure (UnitAddTorus (Fin d))) ℂ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply le_antisymm
  · exact eLpNorm_mono_measure _ (le_of_eq (sourceMeasure_eq_volume d))
  · exact eLpNorm_mono_measure _ (le_of_eq (sourceMeasure_eq_volume d).symm)

private theorem cutoffTensorMultiplier_hasSum {d : ℕ}
    (φ : AdmissibleCutoff) (k : Fin d → ℤ) :
    HasSum (fun s : Fin d → ℕ => ∏ i, scalarBlock φ (s i) (k i : ℝ)) 1 := by
  simpa [BrownianSharp.AlignmentPeriodicCutoffPartition.tensorMultiplier] using
    BrownianSharp.AlignmentPeriodicCutoffPartition.tensorMultiplier_hasSum φ k

private theorem l1CutoffBlock_coefficient {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (f : UnitAddTorus (Fin d) → ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (l1CutoffBlock φ s f) k =
      ((∏ i, scalarBlock φ (s i) (k i:ℝ) : ℝ) : ℂ) * l1CutoffFourierCoeff f k := by
  rw [l1CutoffBlock, fourierPolynomial_coefficient]
  split_ifs with hk
  · simpa only [Complex.ofReal_prod]
  · have hnot : ¬ ∀ i, k i ∈ Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1)) := by
      simpa [frequencyBox] using hk
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    have hout : (2:ℝ)^(s i+1) ≤ |(k i:ℝ)| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hi
      rcases hi with hi | hi
      · have h : (k i:ℝ) < -((2:ℝ)^(s i+1)) := by exact_mod_cast hi
        exact (by linarith : (2:ℝ)^(s i+1) ≤ -(k i:ℝ)).trans (neg_le_abs _)
      · have h : (2:ℝ)^(s i+1) < (k i:ℝ) := by exact_mod_cast hi
        exact h.le.trans (le_abs_self _)
    have hz := scalarBlock_eq_zero_of_two_pow_le_abs φ (s i) hout
    have hprod : ∏ j, scalarBlock φ (s j) (k j:ℝ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    have hprodC : ((∏ j, scalarBlock φ (s j) (k j:ℝ) : ℝ) : ℂ) = 0 := by
      exact_mod_cast hprod
    rw [hprodC]
    simp

private theorem l1CutoffBlock_l2_bound {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (hp : 2 ≤ p) (r : ℝ) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : l1CutoffWeightedBlockNorm φ p r s f ≤ 1) :
    ‖(l1CutoffBlock φ s f).toLp 2
      (sourceMeasure d) ℂ‖ ≤ (2:ℝ)^(-r * ∑ i, (s i:ℝ)) := by
  let A : ℝ := (2:ℝ)^(r * ∑ i, (s i:ℝ))
  have hA : 0 < A := by dsimp [A]; positivity
  have hweight : ENNReal.ofReal A ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hA
  have hweighttop : ENNReal.ofReal A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hquot : eLpNorm (l1CutoffBlock φ s f) p (sourceMeasure d) ≤ ENNReal.ofReal (1/A) := by
    calc
      _ ≤ 1 / ENNReal.ofReal A := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hweight) (Or.inl hweighttop)]
        simpa [l1CutoffWeightedBlockNorm, A, mul_comm] using hf
      _ = ENNReal.ofReal (1/A) := by
        simpa using (ENNReal.ofReal_div_of_pos (x:=1) hA).symm
  have h2 : eLpNorm (l1CutoffBlock φ s f) 2 (sourceMeasure d) ≤
      eLpNorm (l1CutoffBlock φ s f) p (sourceMeasure d) := eLpNorm_le_eLpNorm_of_exponent_le hp
  have hfinite : eLpNorm (l1CutoffBlock φ s f) 2 (sourceMeasure d) < ⊤ :=
    lt_of_le_of_lt (h2.trans hquot) ENNReal.ofReal_lt_top
  have hfiniteP : eLpNorm (l1CutoffBlock φ s f) p (sourceMeasure d) < ⊤ :=
    lt_of_le_of_lt hquot ENNReal.ofReal_lt_top
  have hnorm : ‖(l1CutoffBlock φ s f).toLp 2 (sourceMeasure d) ℂ‖ =
      (eLpNorm (l1CutoffBlock φ s f) 2 (sourceMeasure d)).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _))
  have hreal : (eLpNorm (l1CutoffBlock φ s f) 2 (sourceMeasure d)).toReal ≤ 1/A := by
    calc
      _ ≤ (eLpNorm (l1CutoffBlock φ s f) p (sourceMeasure d)).toReal :=
        ENNReal.toReal_mono (ne_of_lt hfiniteP) h2
      _ ≤ (ENNReal.ofReal (1/A)).toReal := ENNReal.toReal_mono (by simp) hquot
      _ = 1/A := ENNReal.toReal_ofReal (by positivity)
  rw [hnorm]
  have htarget : 1/A = (2:ℝ)^(-r * ∑ i, (s i:ℝ)) := by
    dsimp [A]
    rw [one_div, ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  exact hreal.trans_eq htarget

private theorem l1CutoffBlock_sup_bound {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (hp : 2 ≤ p) (r : ℝ) (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1) :
    ‖l1CutoffBlock φ s f‖ ≤ Real.sqrt ((5:ℝ)^d) *
      ((2:ℝ)^(1/2-r))^(∑ i,s i) := by
  have hs := AlignmentTrigonometricL2.fourierPolynomial_sup_le_sqrt_card_L2
    (frequencyBox s) (fun k =>
      ((∏ i, scalarBlock φ (s i) (k i:ℝ) : ℝ) : ℂ) * l1CutoffFourierCoeff f k)
  have hs' : ‖l1CutoffBlock φ s f‖ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
      ‖(l1CutoffBlock φ s f).toLp 2 (sourceMeasure d) ℂ‖ := by
    have := hs
    have hn := l1CutoffBlock_toLp_norm_eq_volume φ s f
    rw [hn]
    simpa [l1CutoffBlock] using this
  have hL2 := l1CutoffBlock_l2_bound φ p hp r s f (hf s)
  calc
    _ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
        ‖(l1CutoffBlock φ s f).toLp 2 (sourceMeasure d) ℂ‖ := hs'
    _ ≤ Real.sqrt ((5:ℝ)^d * (2:ℝ)^(∑ i,s i)) *
        (2:ℝ)^(-r * ∑ i,(s i:ℝ)) := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt (frequencyBox_card_real_le s)
      · exact hL2
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      rw [← Nat.cast_sum]
      exact sqrt_dyadic_weight_identity d _ r

private theorem l1CutoffBlocks_summable {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (hp : 2 ≤ p) (r : ℝ) (hr : 1/2 < r)
    (f : UnitAddTorus (Fin d) → ℝ)
    (hf : ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1) :
    Summable (fun s : Fin d → ℕ => l1CutoffBlock φ s f) := by
  have hq0 : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hs := (summable_shape_geometric d hq0 hq1).mul_left (Real.sqrt ((5:ℝ)^d))
  exact Summable.of_norm_bounded hs (fun s => l1CutoffBlock_sup_bound φ p hp r s f hf)

private theorem l1CutoffBlocks_sum_fourierCoeff {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (hp : 2 ≤ p) (r : ℝ)
    (hr : 1/2 < r) (f : UnitAddTorus (Fin d) → ℝ)
    (hf : ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1)
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      ((∑' s : Fin d → ℕ, l1CutoffBlock φ s f) : C(UnitAddTorus (Fin d), ℂ)) k =
      l1CutoffFourierCoeff f k := by
  have hs := l1CutoffBlocks_summable φ p hp r hr f hf
  have h1 := (fourierCoefficientCLM k).hasSum hs.hasSum
  have h2 := (Complex.ofRealCLM.hasSum
    (cutoffTensorMultiplier_hasSum φ k)).mul_right (l1CutoffFourierCoeff f k)
  have hblock : ∀ s, UnitAddTorus.mFourierCoeff (l1CutoffBlock φ s f) k =
      ((∏ i, scalarBlock φ (s i) (k i:ℝ) : ℝ) : ℂ) * l1CutoffFourierCoeff f k :=
    fun s => l1CutoffBlock_coefficient φ s f k
  simp only [fourierCoefficientCLM_apply, hblock] at h1
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h2
  exact h1.unique h2

/-- Every integrable L¹ source in an admissible-cutoff Nikolsky ball has a
continuous periodic representative when `p ≥ 2` and `r > 1/2`. -/
theorem l1CutoffNikolsky_has_continuous_rep {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (hp : 2 ≤ p)
    (r : ℝ) (hr : 1/2 < r) (f : UnitAddTorus (Fin d) → ℝ)
    (hf : Integrable f (sourceMeasure d))
    (hball : ∀ s, l1CutoffWeightedBlockNorm φ p r s f ≤ 1) :
    ∃ g : RealPeriodic d,
      f =ᵐ[sourceMeasure d] (fun x => g x) ∧ NikolskyUnitBall φ p r g := by
  classical
  let u : C(UnitAddTorus (Fin d), ℂ) := ∑' s : Fin d → ℕ, l1CutoffBlock φ s f
  have hs := l1CutoffBlocks_summable φ p hp r hr f hball
  have hfV : Integrable f (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [sourceMeasure_eq_volume] using hf
  have huInt : Integrable (fun x => u x) (volume : Measure (UnitAddTorus (Fin d))) := by
    exact u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfC : Integrable (fun x => (f x : ℂ)) (volume : Measure (UnitAddTorus (Fin d))) :=
    Complex.ofRealCLM.integrable_comp hfV
  have hsourceCoeff : ∀ k : Fin d → ℤ,
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k = l1CutoffFourierCoeff f k := fun _ => rfl
  have hsumCoeff := l1CutoffBlocks_sum_fourierCoeff φ p hp r hr f hball
  have hsourceAE : (fun x => (f x : ℂ)) =ᵐ[sourceMeasure d] fun x => u x := by
    exact ae_eq_complex_tsum_of_block_telescope (fun x => (f x : ℂ)) hfC
      (fun s => l1CutoffBlock φ s f) hs (l1CutoffFourierCoeff f)
      (fun s k => ∏ i, scalarBlock φ (s i) (k i:ℝ)) hsourceCoeff
      (fun s k => l1CutoffBlock_coefficient φ s f k)
      (fun k => cutoffTensorMultiplier_hasSum φ k) huInt
  have himAE : (fun x => (u x).im) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hsourceAE] with x hx
    rw [← hx]
    simp
  have him : ∀ x, (u x).im = 0 := by
    have hEq := (Continuous.ae_eq_iff_eq (volume : Measure (UnitAddTorus (Fin d)))
      (Complex.continuous_im.comp u.continuous) continuous_const).mp himAE
    intro x
    exact congrFun hEq x
  let g : RealPeriodic d := ⟨fun x => (u x).re, Complex.continuous_re.comp u.continuous⟩
  have hu : complexifyContinuous g = u := by
    ext x
    apply Complex.ext
    · rfl
    · simpa [complexifyContinuous, g] using (him x).symm
  have hcoeff : ∀ k : Fin d → ℤ,
      l1CutoffFourierCoeff f k = realPeriodicFourierCoeff g k := by
    intro k
    calc
      l1CutoffFourierCoeff f k = UnitAddTorus.mFourierCoeff u k := (hsumCoeff k).symm
      _ = UnitAddTorus.mFourierCoeff (complexifyContinuous g) k := by rw [hu]
      _ = realPeriodicFourierCoeff g k := by
        change UnitAddTorus.mFourierCoeff (fun x => (g x : ℂ)) k = _
        rfl
  refine ⟨g, ?_, ?_⟩
  · have hrealAE : f =ᵐ[volume] fun x => g x := by
      filter_upwards [hsourceAE] with x hx
      apply Complex.ofReal_injective
      calc
        (f x : ℂ) = u x := hx
        _ = (g x : ℂ) := by change u x = complexifyContinuous g x; rw [hu]
    exact ae_local_to_source hrealAE
  · intro s
    have hblock : l1CutoffBlock φ s f = admissibleBlock φ s g := by
      unfold l1CutoffBlock admissibleBlock
      congr 1
      funext k
      change (∏ i, (scalarBlock φ (s i) (k i:ℝ) : ℂ)) * l1CutoffFourierCoeff f k = _
      rw [hcoeff k]
    have hsource := hball s
    change AlignmentPeriodicCutoffClasses.weightedBlockNorm φ p r s g ≤ 1
    unfold AlignmentPeriodicCutoffClasses.weightedBlockNorm
    rw [← hblock, BrownianSharp.unitAddTorus_volume_eq_productHaar d]
    simpa [l1CutoffWeightedBlockNorm, sourceMeasure] using hsource

/-- The full L¹ Nikolsky image is the continuous-ball image in the range
`p ≥ 2`, `r > 1/2`; the reverse inclusion is the direct `toLp` embedding. -/
theorem fullL1NikolskyImage_eq_continuous {d : ℕ}
    (φ : AdmissibleCutoff) (p : ℝ≥0∞) (hp : 2 ≤ p)
    (r : ℝ) (hr : 1/2 < r) :
    fullL1NikolskyImage φ p r =
      Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall φ p r f} := by
  ext v
  constructor
  · intro hv
    letI : IsProbabilityMeasure (ambientVolume d) := by
      dsimp [ambientVolume]
      infer_instance
    rcases hv with ⟨u, hu, hAE⟩
    have hsource : ∀ s, l1CutoffWeightedBlockNorm φ p r s (fun x => u x) ≤ 1 := by
      exact hu
    have hInt : Integrable (fun x => u x) (sourceMeasure d) :=
      (Lp.memLp u).integrable (by norm_num)
    obtain ⟨g,hrep,hball⟩ := l1CutoffNikolsky_has_continuous_rep φ p hp r hr
      (fun x => u x) hInt hsource
    have hglobal : (fun x => u x) =ᵐ[ambientVolume d] fun x => g x :=
      ae_source_to_ambient hrep
    have hvAE : (fun x => (u x : ℝ)) =ᵐ[sourceMeasure d] fun x => v x :=
      ae_ambient_to_source hAE
    have hrep' : (fun x => (g x : ℝ)) =ᵐ[ambientVolume d] fun x => v x :=
      hglobal.symm.trans (ae_source_to_ambient hvAE)
    refine ⟨g, hball, ?_⟩
    apply Lp.ext
    filter_upwards [hrep', ContinuousMap.coeFn_toLp
      (p := ⊤) (𝕜 := ℝ) (μ := ambientVolume d) g] with x hx hto
    exact hto.trans hx
  · intro hv
    exact continuousNikolskyImage_subset_fullL1 φ p r hv

end BrownianSharp.AlignmentPeriodicL1AdmissibleReconstruction
