import BrownianSharp.NativeNikolskySynthesis
import BrownianSharp.SmoothClassScaling
import BrownianSharp.PeriodicNativeEntropy
import BrownianSharp.SmoothSobolevHigherPMean

/-! Final Nikolsky class-mass endpoint for the periodic native synthesis. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BrownianSharp

open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

private theorem dyadic_inverse_nat_pow (a K : ℕ) :
    (((2:ℝ)^a)⁻¹)^K = (2:ℝ)^(-(a:ℝ)*(K:ℝ)) := by
  have hbase : (2:ℝ)^a = (2:ℝ)^(a:ℝ) := by simp
  rw [hbase, ← Real.rpow_natCast]
  rw [Real.inv_rpow (by positivity : 0 ≤ (2:ℝ)^(a:ℝ))]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

private theorem dyadic_inverse_gap_mul (s t K : ℕ) (hst : s < t) :
    (((2:ℝ)^t)⁻¹)^K * (2:ℝ)^(s*K) =
      (2:ℝ)^(-((K:ℝ) * ((t-s:ℕ):ℝ))) := by
  rw [dyadic_inverse_nat_pow t K, ← Real.rpow_natCast (2:ℝ) (s*K)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  have hsub : s + (t-s) = t := Nat.add_sub_of_le (Nat.le_of_lt hst)
  have hsubR : (s:ℝ) + ((t-s:ℕ):ℝ) = (t:ℝ) := by exact_mod_cast hsub
  rw [← hsubR]
  simp only [Nat.cast_mul]
  ring

def nativeNikolskyShapeWeightReal {d : ℕ} (s t : Fin d → ℕ)
    (r : ℝ) (K : ℕ) : ℝ :=
  ∏ i : Fin d, if t i ≤ s i then
    (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
  else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))

private theorem dyadicShapeWeightedFactor_eq {d : ℕ}
    (s t : Fin d → ℕ) (r : ℝ) (K n : ℕ)
    (hsum : ∑ i, s i = n) :
    (2:ℝ)^(r * ∑ i, (t i:ℝ)) *
      (∏ i : Fin d, if s i < t i then
        (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) else 1) =
    (2:ℝ)^(r*(n:ℝ)) * nativeNikolskyShapeWeightReal s t r K := by
  have hcoord : ∀ i : Fin d,
      (2:ℝ)^(r*(t i:ℝ)) * (if s i < t i then
        (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) else 1) =
      (2:ℝ)^(r*(s i:ℝ)) *
        (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
          else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))) := by
    intro i
    by_cases hst : s i < t i
    · have hgap : (s i:ℝ) + ((t i-s i:ℕ):ℝ) = (t i:ℝ) := by
        exact_mod_cast (Nat.add_sub_of_le (Nat.le_of_lt hst))
      simp [hst, Nat.not_le_of_gt hst]
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      rw [← hgap]
      ring
    · have hts : t i ≤ s i := Nat.le_of_not_gt hst
      have hgap : (t i:ℝ) + ((s i-t i:ℕ):ℝ) = (s i:ℝ) := by
        exact_mod_cast (Nat.add_sub_of_le hts)
      simp [hst, hts]
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      rw [← hgap]
      ring
  have hprod : (∏ i : Fin d, (2:ℝ)^(r*(t i:ℝ))) *
      (∏ i : Fin d, if s i < t i then
        (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) else 1) =
      (∏ i : Fin d, (2:ℝ)^(r*(s i:ℝ))) * nativeNikolskyShapeWeightReal s t r K := by
    calc
      _ = ∏ i : Fin d, ((2:ℝ)^(r*(t i:ℝ)) *
          (if s i < t i then (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) else 1)) :=
            (Finset.prod_mul_distrib).symm
      _ = ∏ i : Fin d, ((2:ℝ)^(r*(s i:ℝ)) *
          (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
            else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ)))) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hcoord i
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        rfl
  have ht : (2:ℝ)^(r * ∑ i, (t i:ℝ)) =
      ∏ i : Fin d, (2:ℝ)^(r*(t i:ℝ)) := by
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
  have hs' : ∏ i : Fin d, (2:ℝ)^(r*(s i:ℝ)) = (2:ℝ)^(r*(n:ℝ)) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum]
  rw [ht, ← hs']
  exact hprod

private theorem finset_prod_rpow_of_nonneg {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (p : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ p = ∏ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      rw [Real.mul_rpow (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))]
      rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem prod_le_prod_nonneg_real {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (hle i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hle j (Finset.mem_insert_of_mem hj)))
        (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (hg i (Finset.mem_insert_self _ _))

private theorem eLpNorm_le_of_integral_bound {d : ℕ}
    (f : C(UnitAddTorus (Fin d), ℂ)) (p B : ℝ) (hp : 0 < p)
    (hB : 0 ≤ B)
    (hInt : (∫ x : UnitAddTorus (Fin d), ‖f x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ B) :
    eLpNorm f (ENNReal.ofReal p)
      (volume : Measure (UnitAddTorus (Fin d))) ≤ ENNReal.ofReal (B ^ (1 / p)) := by
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
  let g : UnitAddTorus (Fin d) → ℝ := fun x => ‖f x‖ ^ p
  have hgcont : Continuous g := by
    dsimp [g]
    exact (f.continuous.norm).rpow_const (fun _ => Or.inr (le_of_lt hp))
  have hgmeas : AEStronglyMeasurable g μ := hgcont.aestronglyMeasurable
  have hgint : Integrable g μ := by
    apply Integrable.of_bound hgmeas (‖f‖ ^ p)
    filter_upwards [] with x
    dsimp [g]
    have hn : ‖f x‖ ≤ ‖f‖ := f.norm_coe_le_norm x
    have hp' : 0 ≤ p := le_of_lt hp
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    exact Real.rpow_le_rpow (norm_nonneg _) hn hp'
  have hnonneg : 0 ≤ᵐ[μ] g := ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg _) p)
  have hlint : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ENNReal.ofReal (∫ x, g x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hgint hnonneg).symm
  have hmeasure : (volume : Measure (UnitAddTorus (Fin d))) = μ :=
    unitAddTorus_volume_eq_productHaar d
  rw [hmeasure]
  have hmem : MemLp f (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    filter_upwards [] with x
    exact f.norm_coe_le_norm x
  have hnorm := lpNorm_eq_integral_norm_rpow_toReal
    (f := f) (p := ENNReal.ofReal p) (ENNReal.ofReal_pos.mpr hp).ne'
    (by simp : ENNReal.ofReal p ≠ ∞) (μ := μ) f.continuous.aestronglyMeasurable
  have hnorm' : lpNorm f (ENNReal.ofReal p) μ = (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
    simpa [ENNReal.toReal_ofReal hp.le] using hnorm
  rw [← ofReal_lpNorm hmem, hnorm']
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hInt
    (by positivity : 0 ≤ 1 / p))

theorem weightedBlockNorm_le_of_integral_bound {d : ℕ}
    (f : RealPeriodic d) (t : Fin d → ℕ) (p r B : ℝ)
    (hp : 0 < p) (hB : 0 ≤ B)
    (hInt : (∫ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t f x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ B) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t f ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ)) * B ^ (1 / p)) := by
  unfold SmoothResolution.weightedBlockNorm
  have hnorm := eLpNorm_le_of_integral_bound (SmoothResolution.block t f)
    p B hp hB hInt
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ))) *
        ENNReal.ofReal (B ^ (1/p)) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hnorm) bot_le
    _ = ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ)) * B ^ (1/p)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        0 ≤ (2 : ℝ) ^ (r * ∑ i, (t i : ℝ)))]

theorem fixedShape_weightedBlockNorm_le_nativeDecay {d : ℕ}
    (s t : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p r : ℝ) (hp : 1 ≤ p) (K : ℕ) (hK : Even K) (hKpos : 0 < K)
    (Lscalar Lprofile Cderiv : ℝ)
    (hLscalar : 0 ≤ Lscalar) (hLprofile : 0 ≤ Lprofile)
    (hCderiv : 0 ≤ Cderiv)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ (q : ℕ), 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ Cderiv) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (fixedShapeSynthesis s c) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ)) *
        ((∏ i : Fin d, if s i < t i then
          ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar) ^ p *
          (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ *
            ((if s i < t i then Cderiv else 1) *
              (2 : ℝ) ^ (s i * (if s i < t i then K else 0))) ^ p) *
          ∑ j : DyadicShapeCell d s, |c j| ^ p) ^ (1 / p)) := by
  let B := (∏ i : Fin d, if s i < t i then
      ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar) ^ p *
    (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ *
      ((if s i < t i then Cderiv else 1) *
        (2 : ℝ) ^ (s i * (if s i < t i then K else 0))) ^ p) *
    ∑ j : DyadicShapeCell d s, |c j| ^ p
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hInt := fixedShapeBlock_nativeDecay_integral s t c p hp K hK hKpos
    Lscalar Lprofile Cderiv hLscalar hLprofile hCderiv hscalar hprofile hderiv
  have hInt' : (∫ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ B := by
    simpa [B] using hInt
  change SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
      (fixedShapeSynthesis s c) ≤ _
  exact weightedBlockNorm_le_of_integral_bound (fixedShapeSynthesis s c) t p r B
    (by linarith [hp]) hB hInt'

def nativeNikolskyShapeWeight {d : ℕ} (t : Fin d → ℕ)
    (qlow qhigh : ℝ≥0∞) (s : Fin d → ℕ) : ℝ≥0∞ :=
  ∏ i : Fin d, if t i ≤ s i then qlow ^ (s i - t i)
    else qhigh ^ (t i - s i)

theorem periodicNative_weightedBlockNorm_le_of_shapeEnvelope
    {d n : ℕ} (x : LayerIndex d n → ℝ) (p r C : ℝ) (hp : 1 ≤ p)
    (qlow qhigh : ℝ≥0∞) (t : Fin d → ℕ)
    (hqlow : qlow < 1) (hqhigh : qhigh < 1)
    (hshape : ∀ s : Shape d n,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ))) *
          nativeNikolskyShapeWeight t qlow qhigh (fun i => s.1 i)) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
      (periodicNativeSynthesisLinear x) ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ))) *
        (((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹) ^ d) := by
  have htri := periodicNative_weightedBlockNorm_le_sum_shapes p hp r t x
  calc
    _ ≤ ∑ s : Shape d n,
        SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
          (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) := htri
    _ ≤ ∑ s : Shape d n,
        ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ))) *
          nativeNikolskyShapeWeight t qlow qhigh (fun i => s.1 i) := by
      exact Finset.sum_le_sum fun s hs => hshape s
    _ = ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ))) *
          ∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh (fun i => s.1 i) := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ))) *
          (((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹) ^ d) := by
      gcongr
      simpa [nativeNikolskyShapeWeight] using
        (shape_twoSided_geometric_sum_le t qlow qhigh hqlow hqhigh)

/-- Once a fixed-shape estimate has been converted to the two-sided
coordinate profile, its sum over native shapes has a dimension-only loss.
This is the exact aggregation interface used by the final Nikolsky endpoint;
in particular, it does not pay the number of grade-`n` shapes. -/
theorem periodicNative_weightedBlockNorm_le_of_shapeEnvelope_uniform
    {d n : ℕ} (x : LayerIndex d n → ℝ) (p r C₀ : ℝ) (hp : 1 ≤ p)
    (qlow qhigh : ℝ≥0∞) (t : Fin d → ℕ)
    (hqlow : qlow < 1) (hqhigh : qhigh < 1)
    (hshape : ∀ s : Shape d n,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) ≤
        ENNReal.ofReal (C₀ * (2 : ℝ) ^ (r * (n:ℝ))) *
          nativeNikolskyShapeWeight t qlow qhigh (fun i => s.1 i)) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
      (periodicNativeSynthesisLinear x) ≤
      ENNReal.ofReal (C₀ * (2 : ℝ) ^ (r * (n:ℝ))) *
        (((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹) ^ d) :=
  periodicNative_weightedBlockNorm_le_of_shapeEnvelope x p r C₀ hp
    qlow qhigh t hqlow hqhigh hshape

theorem periodicNativeNikolsky_class_mass_of_uniform_block_bound
    {d : ℕ} (hd : 2 ≤ d) (p r C : ℝ) (hp : 1 < p)
    (hr : 0 < r) (hC : 0 < C)
    (hbound : ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      x ∈ smoothShapeJointGoodEvent p Finset.univ → ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (periodicNativeSynthesisLinear x) ≤
          ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ)))) :
    ∀ n : ℕ,
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | ((1/(2*C))*periodicSynthesisScale d n r (1/2)) •
            periodicNativeSynthesisLinear x ∈
              {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
                (ENNReal.ofReal p) r f}} := by
  intro n
  let a : ℝ := 1/(2*C)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < a * periodicSynthesisScale d n r (1/2) :=
    mul_pos ha (periodicSynthesisScale_pos (by omega) r (1/2))
  have hclass : ∀ x : LayerIndex d n → ℝ,
      x ∈ smoothShapeJointGoodEvent p Finset.univ →
      (a*periodicSynthesisScale d n r (1/2)) •
        periodicNativeSynthesisLinear x ∈
          {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
            (ENNReal.ofReal p) r f} := by
    intro x hx
    have hscale : periodicSynthesisScale d n r (1/2) =
        (2:ℝ)^(-r*(n:ℝ)) := by
      simp [periodicSynthesisScale, Real.rpow_zero]
    have hnorm : ∀ t : Fin d → ℕ,
        SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
          ((a*periodicSynthesisScale d n r (1/2)) •
            periodicNativeSynthesisLinear x) ≤ 1 := by
      intro t
      rw [weightedBlockNorm_smul hA, hscale]
      have hbase := hbound n x hx t
      have hpow : (2:ℝ)^(-r*(n:ℝ)) * (2:ℝ)^(r*(n:ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        simp
      have hmul : (a*(2:ℝ)^(-r*(n:ℝ))) *
          (C*(2:ℝ)^(r*(n:ℝ))) = a*C := by
        calc
          _ = a*C*((2:ℝ)^(-r*(n:ℝ))*(2:ℝ)^(r*(n:ℝ))) := by ring
          _ = a*C := by rw [hpow, mul_one]
      have hprod : ENNReal.ofReal (a*(2:ℝ)^(-r*(n:ℝ))) *
          ENNReal.ofReal (C*(2:ℝ)^(r*(n:ℝ))) = ENNReal.ofReal (a*C) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a*(2:ℝ)^(-r*(n:ℝ))), hmul]
      calc
        _ ≤ ENNReal.ofReal (a*(2:ℝ)^(-r*(n:ℝ))) *
              ENNReal.ofReal (C*(2:ℝ)^(r*(n:ℝ))) := by
                gcongr
        _ = ENNReal.ofReal (a*C) := hprod
        _ ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          dsimp [a]
          have heq : 1 / (2*C) * C = (1:ℝ)/2 := by
            field_simp
          rw [heq]
          norm_num
    change SmoothResolution.NikolskyUnitBall (ENNReal.ofReal p) r
      ((a*periodicSynthesisScale d n r (1/2)) •
        periodicNativeSynthesisLinear x)
    simp [SmoothResolution.NikolskyUnitBall, SmoothResolution.BesovUnitBall]
    simpa using hnorm
  have hmass := smoothAllShapesCoefficientCutoff_mass (d:=d) (n:=n)
    (by omega : 0 < d)
    (lt_trans (by norm_num : (0:ℝ) < 1) hp)
  have hsub : smoothShapeJointGoodEvent p Finset.univ ⊆
      {x : LayerIndex d n → ℝ | (a*periodicSynthesisScale d n r (1/2)) •
        periodicNativeSynthesisLinear x ∈
          {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
            (ENNReal.ofReal p) r f}} := by
    intro x hx
    exact hclass x hx
  have hfinal : (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
      productStandardGaussian (LayerIndex d n)
        {x : LayerIndex d n → ℝ | (a*periodicSynthesisScale d n r (1/2)) •
          periodicNativeSynthesisLinear x ∈
            {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
              (ENNReal.ofReal p) r f}} := calc
    _ ≤ productStandardGaussian (LayerIndex d n)
        (smoothShapeJointGoodEvent p Finset.univ) := hmass
    _ ≤ productStandardGaussian (LayerIndex d n)
        {x : LayerIndex d n → ℝ | (a*periodicSynthesisScale d n r (1/2)) •
          periodicNativeSynthesisLinear x ∈
            {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
            (ENNReal.ofReal p) r f}} := measure_mono hsub
  simpa [a] using hfinal

theorem periodicNikolsky_entropy_of_native_uniform_block_bound
    {d : ℕ} (hd : 2 ≤ d) (p r C : ℝ) (hp : 1 < p)
    (hr : 0 < r) (hC : 0 < C)
    (hbound : ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      x ∈ smoothShapeJointGoodEvent p Finset.univ → ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (periodicNativeSynthesisLinear x) ≤
          ENNReal.ofReal (C * (2 : ℝ) ^ (r * (n:ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        ((r+1/2)*((d-1:ℕ):ℝ)+1/2)) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
              (ENNReal.ofReal p) r f} := by
  have hclass := periodicNativeNikolsky_class_mass_of_uniform_block_bound
    hd p r C hp hr hC hbound
  have hclass' : ∀ n : ℕ, 0 ≤ n →
      (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | ((1/(2*C))*periodicSynthesisScale d n r (1/2)) •
            periodicNativeSynthesisLinear x ∈
              {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
                (ENNReal.ofReal p) r f}} := by
    intro n _
    exact hclass n
  obtain ⟨c,hc,k₀,hk₀,hent⟩ := periodic_entropy_rate_of_scaled_native_class_mass
    hd {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
      (ENNReal.ofReal p) r f} r (1/2) (1/(2*C)) hr
      (by positivity) 0 hclass'
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  have hpower : r*((d-1:ℕ):ℝ)+(1/2+(1/2)*((d-1:ℕ):ℝ)) =
      (r+1/2)*((d-1:ℕ):ℝ)+1/2 := by ring
  simpa only [hpower] using hent k hk

end BrownianSharp
