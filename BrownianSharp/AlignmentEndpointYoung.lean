import BrownianSharp.AlignmentEndpointNativeAllTheta
import BrownianSharp.NativeNikolskyEndpoint
import BrownianSharp.NativeNikolskyENNRealProfile
import BrownianSharp.AlignmentEndpointCoefficientBox
import BrownianSharp.AlignmentEndpointGaussianBox
import Mathlib.Analysis.MeanInequalities
import BrownianSharp.SmoothClassScaling
import BrownianSharp.SmoothClassEvents
import BrownianSharp.AlignmentExponentialBoxEntropy

set_option maxHeartbeats 3200000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 100000

/-! Powered discrete Young aggregation for the periodic endpoint profile. -/
noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockVariance
open MeasureTheory

/-- Weighted Hölder gives the powered Jensen bound for any finite weighted sum. -/
theorem endpoint_weighted_powered_sum_le {ι : Type*} (s : Finset ι)
    (w f : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * f i) ^ p ≤
      (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, w i * f i ^ p := by
  by_cases hpeq : p = 1
  · subst p
    simp
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpeq)
  have hp0 : 0 < p := by linarith
  have h := ENNReal.inner_le_weight_mul_Lp_of_nonneg s hp w f
  have hpow := ENNReal.rpow_le_rpow h hp0.le
  have hmul :
      ((∑ i ∈ s, w i) ^ (1 - p⁻¹) *
        (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹) ^ p =
      (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, w i * f i ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have h1 : (1 - p⁻¹) * p = p - 1 := by field_simp
    have h2 : p⁻¹ * p = 1 := by field_simp
    rw [h1, h2, ENNReal.rpow_one]
  rw [hmul] at hpow
  exact hpow

/-- Discrete weighted Young inequality on a countable target: row mass controls
convolution power, and a uniform column-mass bound controls the output sum. -/
theorem endpoint_discrete_weighted_young
    {S T : Type*} [Fintype S] [Countable T] [DecidableEq S]
    (w : S → T → ℝ≥0∞) (g : S → ℝ≥0∞) (A : ℝ≥0∞) {p : ℝ}
    (hp : 1 ≤ p)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hrow : ∀ t, ∑ s : S, w s t ≤ A)
    (hcol : ∀ s, (∑' t : T, w s t) ≤ A) :
    (∑' t : T, (∑ s : S, w s t * g s) ^ p) ≤
      A ^ p * ∑ s : S, g s ^ p := by
  classical
  have hp0 : 0 < p := by linarith
  have hpoint (t : T) :
      (∑ s : S, w s t * g s) ^ p ≤
        A ^ (p - 1) * ∑ s : S, w s t * g s ^ p := by
    have h := endpoint_weighted_powered_sum_le Finset.univ
      (fun s => w s t) g hp
    calc
      _ ≤ (∑ s : S, w s t) ^ (p - 1) *
          ∑ s : S, w s t * g s ^ p := h
      _ ≤ A ^ (p - 1) * ∑ s : S, w s t * g s ^ p := by
        gcongr
        · exact hrow t
  have hsum := ENNReal.tsum_le_tsum hpoint
  calc
    _ ≤ ∑' t : T, A ^ (p - 1) * ∑ s : S, w s t * g s ^ p := hsum
    _ = A ^ (p - 1) * ∑' t : T, ∑ s : S, w s t * g s ^ p := by
      rw [ENNReal.tsum_mul_left]
    _ = A ^ (p - 1) * ∑ s : S, g s ^ p * ∑' t : T, w s t := by
      congr 1
      have hfin (t : T) :
          (∑ s : S, w s t * g s ^ p) =
            ∑' s : S, w s t * g s ^ p :=
        (tsum_fintype (L := .unconditional _) _).symm
      simp_rw [hfin]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_right]
      simp [mul_comm]
    _ ≤ A ^ (p - 1) * ∑ s : S, g s ^ p * A := by
      gcongr
      exact hcol _
    _ = A ^ p * ∑ s : S, g s ^ p := by
      have hpow : A ^ (p - 1) * A = A ^ p := by
        calc
          A ^ (p - 1) * A = A ^ (p - 1) * A ^ (1:ℝ) := by rw [ENNReal.rpow_one]
          _ = A ^ ((p - 1) + 1) := (ENNReal.rpow_add _ _ hA0 hAtop).symm
          _ = A ^ p := by congr 2 <;> ring
      calc
        A ^ (p - 1) * ∑ s : S, g s ^ p * A =
            (A ^ (p - 1) * A) * ∑ s : S, g s ^ p := by
              rw [← Finset.sum_mul]
              ring
        _ = A ^ p * ∑ s : S, g s ^ p := by rw [hpow]

/-- The unit source indicator has powered Young budget equal to the source
cardinality. This is the exact shape-count factor needed by the coefficient
box route. -/
theorem endpoint_discrete_weighted_young_unit
    {S T : Type*} [Fintype S] [Countable T] [DecidableEq S]
    (w : S → T → ℝ≥0∞) (A B : ℝ≥0∞) {p : ℝ}
    (hp : 1 ≤ p) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hrow : ∀ t, ∑ s : S, w s t ≤ A)
    (hcol : ∀ s, (∑' t : T, w s t) ≤ A) :
    (∑' t : T, (B * ∑ s : S, w s t) ^ p) ≤
      B ^ p * A ^ p * Fintype.card S := by
  have hp0 : 0 < p := by linarith
  calc
    _ = B ^ p * ∑' t : T, (∑ s : S, w s t) ^ p := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext t
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    _ ≤ B ^ p * (A ^ p * Fintype.card S) := by
      gcongr
      simpa using endpoint_discrete_weighted_young w (fun _ : S => 1) A hp
        hA0 hAtop hrow hcol
    _ = B ^ p * A ^ p * Fintype.card S := by ring

/-- At each fixed target, the geometric endpoint profile has the existing
dimension-only source-shape mass. -/
theorem endpoint_shape_profile_row_sum_le {d n : ℕ}
    (t : Fin d → ℕ) (qlow qhigh : ℝ≥0∞)
    (hqlow : qlow < 1) (hqhigh : qhigh < 1) :
    (∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh s.1) ≤
      ((1 - qlow)⁻¹ + qhigh * (1 - qhigh)⁻¹) ^ d := by
  simpa [nativeNikolskyShapeWeight] using
    (shape_twoSided_geometric_sum_le t qlow qhigh hqlow hqhigh)

/-- The same coordinate profile has the same mass when summed over target
depths for any fixed source. -/
theorem endpoint_shape_profile_column_sum_le {d : ℕ}
    (s : Fin d → ℕ) (qlow qhigh : ℝ≥0∞)
    (hqlow : qlow < 1) (hqhigh : qhigh < 1) :
    (∑' t : Fin d → ℕ, nativeNikolskyShapeWeight t qlow qhigh s) ≤
      ((1 - qlow)⁻¹ + qhigh * (1 - qhigh)⁻¹) ^ d := by
  classical
  let A : ℝ≥0∞ := (1 - qlow)⁻¹ + qhigh * (1 - qhigh)⁻¹
  let f : Fin d → ℕ → ℝ≥0∞ := fun i k =>
    if k ≤ s i then qlow ^ (s i - k) else qhigh ^ (k - s i)
  have hcoord : ∀ i : Fin d, (∑' k : ℕ, f i k) ≤ A := by
    intro i
    have h := NativeLayerThetaBudget.forwardTsum_le_of_pointwise_split
      (s i) qlow qhigh 1 1 hqlow hqhigh (f i)
      (by intro k hk; simp [f, hk])
      (by intro k hk; simp [f, Nat.not_le_of_gt hk])
    simpa [A] using h
  have hfactor :
      (∑' t : Fin d → ℕ, nativeNikolskyShapeWeight t qlow qhigh s) =
        ∏ i : Fin d, ∑' k : ℕ, f i k := by
    change (∑' t : Fin d → ℕ, ∏ i : Fin d, f i (t i)) = _
    rw [NativeLayerThetaBudget.ennreal_tsum_pi_prod]
  rw [hfactor]
  calc
    _ ≤ ∏ _i : Fin d, A := Finset.prod_le_prod (fun i hi => hcoord i)
    _ = A ^ d := by simp [A]

private theorem endpoint_rpow_nat_gap (a : ℝ) (m : ℕ) :
    (2:ℝ)^(a*(m:ℝ)) = ((2:ℝ)^a)^m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- The real profile produced by the inverse/scalar block kernels is exactly
the native Nikolsky profile with dyadic low/high bases. -/
theorem endpoint_profileReal_eq_nativeReal {d : ℕ}
    (s t : Fin d → ℕ) (r : ℝ) (K : ℕ) :
    endpointNikolskyShapeWeightReal s t r K =
      nativeNikolskyRealShapeWeight t
        ((2:ℝ)^(-r)) ((2:ℝ)^(-((K:ℝ)-r))) s := by
  unfold endpointNikolskyShapeWeightReal nativeNikolskyRealShapeWeight
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs with h
  · exact endpoint_rpow_nat_gap (-r) (s i-t i)
  · exact endpoint_rpow_nat_gap (-((K:ℝ)-r)) (t i-s i)

/-- ENNReal profile conversion, retaining the literal dyadic native weight. -/
theorem endpoint_profileENNReal_eq_native {d : ℕ}
    (s t : Fin d → ℕ) (r : ℝ) (K : ℕ) :
    nativeNikolskyShapeWeight t
        (ENNReal.ofReal ((2:ℝ)^(-r)))
        (ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r)))) s =
      ENNReal.ofReal (endpointNikolskyShapeWeightReal s t r K) := by
  let ql : ℝ := (2:ℝ)^(-r)
  let qh : ℝ := (2:ℝ)^(-((K:ℝ)-r))
  have hreal : nativeNikolskyRealShapeWeight t ql qh s =
      endpointNikolskyShapeWeightReal s t r K := by
    simpa only [ql, qh] using (endpoint_profileReal_eq_nativeReal s t r K).symm
  calc
    nativeNikolskyShapeWeight t (ENNReal.ofReal ql) (ENNReal.ofReal qh) s =
        nativeNikolskyENNRealShapeWeight t (ENNReal.ofReal ql) (ENNReal.ofReal qh) s := rfl
    _ = ENNReal.ofReal (nativeNikolskyRealShapeWeight t ql qh s) :=
      nativeNikolskyShapeWeight_eq_ofReal_real t ql qh (by positivity) (by positivity) s
    _ = ENNReal.ofReal (endpointNikolskyShapeWeightReal s t r K) := by rw [hreal]

/-- The actual p=∞ fixed-shape block estimate, expressed in the ENNReal
geometric profile needed by the all-theta Young step. -/
theorem fixedShape_weightedBlockNorm_top_le_endpointProfile
    {d n : ℕ} (s : Fin d → ℕ) (hsum : ∑ i : Fin d, s i = n)
    (t : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (M r Lscalar Lprofile Czero CK : ℝ) (K : ℕ)
    (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (hr : 0 ≤ r) (hK : Even K) (hKpos : 0 < K) (hrK : r < K)
    (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hC0 : 0 ≤ Czero) (hCK : 0 ≤ CK)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ q : ℕ, 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv0 : ∀ y : ℝ, |iteratedDeriv 0 smoothAtom y| ≤ Czero)
    (hderivK : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ CK) :
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
      (fixedShapeSynthesis s c) ≤
      ENNReal.ofReal (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) *
      nativeNikolskyShapeWeight t
        (ENNReal.ofReal ((2:ℝ)^(-r)))
        (ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))) ) s := by
  have hraw := fixedShape_weightedBlockNorm_top_le_endpointProductDecay
    s t c M r Lscalar Lprofile Czero CK K hM hcoeff hr hK hKpos
    hLs hLp hC0 hCK hscalar hprofile hderiv0 hderivK
  have hfactor := endpoint_product_profile_factor s t M r Lscalar Lprofile
    Czero CK K hM hr hK hKpos hrK hLs hLp hC0 hCK hsum
  have hB : 0 ≤ M * (max (Lscalar*Czero) (Lprofile*CK))^d *
      (2:ℝ)^(r*(n:ℝ)) := by positivity
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)) *
        (M * ∏ i : Fin d,
          ((if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
            ((if s i < t i then CK else Czero) *
              (2:ℝ)^(s i*(if s i < t i then K else 0)))))) := hraw
    _ ≤ ENNReal.ofReal (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ)) * endpointNikolskyShapeWeightReal s t r K) :=
          ENNReal.ofReal_le_ofReal hfactor
    _ = ENNReal.ofReal (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
          (2:ℝ)^(r*(n:ℝ))) *
        ENNReal.ofReal (endpointNikolskyShapeWeightReal s t r K) := by
          rw [ENNReal.ofReal_mul hB]
    _ = _ := by
          rw [← endpoint_profileENNReal_eq_native s t r K]

/-- Top-exponent block triangle inequality for the actual native synthesis. -/
theorem endpoint_periodicNative_weightedBlockNorm_top_le_sum_shapes
    {d n : ℕ} (r : ℝ) (t : Fin d → ℕ) (x : LayerIndex d n → ℝ) :
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
      (periodicNativeSynthesisLinear x) ≤
      ∑ a : Shape d n, SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) := by
  classical
  have hdecomp (z : UnitAddTorus (Fin d)) :
      SmoothResolution.block t (periodicNativeSynthesisLinear x) z =
        ∑ a : Shape d n, SmoothResolution.block t
          (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z := by
    have hs := periodicNativeSynthesisLinear_eq_sum_shapes x
    rw [hs]
    change smoothBlockLinear t
      (∑ a : Shape d n, fixedShapeSynthesis (fun i => a.1 i)
        (fun j => x ⟨a,j⟩)) z =
      ∑ a : Shape d n, smoothBlockLinear t
        (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z
    rw [map_sum]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  unfold SmoothResolution.weightedBlockNorm
  rw [show (fun z : UnitAddTorus (Fin d) =>
      SmoothResolution.block t (periodicNativeSynthesisLinear x) z) =
      (fun z => ∑ a : Shape d n, SmoothResolution.block t
        (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) from by
          funext z
          exact hdecomp z]
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i, (t i:ℝ))) *
        ∑ a : Shape d n, eLpNorm
          (fun z => SmoothResolution.block t
            (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
          (⊤ : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
      have htri := MeasureTheory.eLpNorm_sum_le
        (μ := (volume : Measure (UnitAddTorus (Fin d))))
        (p := (⊤ : ℝ≥0∞))
        (f := fun a : Shape d n => fun z : UnitAddTorus (Fin d) =>
          SmoothResolution.block t
          (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
        (s := (Finset.univ : Finset (Shape d n))) (by simp)
      have hsumfun :
          (∑ a : Shape d n, fun z : UnitAddTorus (Fin d) =>
            SmoothResolution.block t
              (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) =
          (fun z => ∑ a : Shape d n, SmoothResolution.block t
            (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) := by
        funext z
        simp
      have htri' : eLpNorm
          (fun z : UnitAddTorus (Fin d) => ∑ a : Shape d n,
            SmoothResolution.block t
              (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
          (⊤ : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) ≤
          ∑ a : Shape d n, eLpNorm
            (fun z => SmoothResolution.block t
              (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
            (⊤ : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
        rw [← hsumfun]
        exact htri
      exact mul_le_mul_of_nonneg_left htri' (by positivity)
    _ = ∑ a : Shape d n,
        ENNReal.ofReal ((2:ℝ)^(r*∑ i, (t i:ℝ))) *
          eLpNorm
            (fun z => SmoothResolution.block t
              (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
            (⊤ : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
      rw [Finset.mul_sum]

/-- Deterministic periodic endpoint: an actual fixed-shape geometric envelope
and its two mass bounds imply the literal ENNReal Besov ball for every
`theta ≥ 1`, including `theta = ∞`. -/
theorem endpoint_periodicBesov_of_shapeProfile
    {d n : ℕ} (x : LayerIndex d n → ℝ) (r : ℝ)
    (theta : ℝ≥0∞) (B A qlow qhigh : ℝ≥0∞)
    (hθ : 1 ≤ theta) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hrow : ∀ t : Fin d → ℕ,
      (∑ s : Shape d n,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A)
    (hcol : ∀ s : Shape d n,
      (∑' t : Fin d → ℕ,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A)
    (hshape : ∀ s : Shape d n, ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) ≤
      B * nativeNikolskyShapeWeight t qlow qhigh s.1)
    (hbudgetNorm : if theta = ⊤ then B * A ≤ 1 else
      B ^ theta.toReal * A ^ theta.toReal * Fintype.card (Shape d n) ≤ 1) :
    SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
      (periodicNativeSynthesisLinear x) := by
  classical
  let envelope : (Fin d → ℕ) → ℝ≥0∞ := fun t =>
    B * ∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh s.1
  have hblock (t : Fin d → ℕ) :
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (periodicNativeSynthesisLinear x) ≤ envelope t := by
    calc
      _ ≤ ∑ s : Shape d n,
          SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
            (fixedShapeSynthesis (fun i => s.1 i) (fun j => x ⟨s,j⟩)) :=
          endpoint_periodicNative_weightedBlockNorm_top_le_sum_shapes r t x
      _ ≤ ∑ s : Shape d n,
          B * nativeNikolskyShapeWeight t qlow qhigh s.1 :=
          Finset.sum_le_sum fun s hs => hshape s t
      _ = envelope t := by
        simp [envelope, Finset.mul_sum]
  have hbudget : if theta = ⊤ then (∀ t, envelope t ≤ 1) else
      ∑' t : Fin d → ℕ, (envelope t) ^ theta.toReal ≤ 1 := by
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hBtop : B * A ≤ 1 := by simpa [htop] using hbudgetNorm
      intro t
      calc
        envelope t ≤ B * A := by
          dsimp [envelope]
          exact mul_le_mul_of_nonneg_left (hrow t) bot_le
        _ ≤ 1 := hBtop
    · simp only [htop, ↓reduceIte]
      have hBfinite : B ^ theta.toReal * A ^ theta.toReal *
          Fintype.card (Shape d n) ≤ 1 := by simpa [htop] using hbudgetNorm
      have hp : 1 ≤ theta.toReal := by
        have hne : theta ≠ ⊤ := htop
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hne).2 hθ
      calc
        _ ≤ B ^ theta.toReal * A ^ theta.toReal *
            Fintype.card (Shape d n) := by
          change (∑' t : Fin d → ℕ,
            (B * ∑ s : Shape d n,
              nativeNikolskyShapeWeight t qlow qhigh s.1)^theta.toReal) ≤ _
          exact endpoint_discrete_weighted_young_unit
              (S := Shape d n) (T := Fin d → ℕ)
              (fun s t => nativeNikolskyShapeWeight t qlow qhigh s.1)
              A B (p := theta.toReal) hp hA0 hAtop hrow hcol
        _ ≤ 1 := hBfinite
  exact besovUnitBall_of_weightedBlockNorm_le_envelope
    (⊤ : ℝ≥0∞) r theta (periodicNativeSynthesisLinear x) hθ
    envelope hbudget hblock

/-- Instantiate the abstract all-theta Besov envelope with the checked
inverse/scalar kernel and smooth-atom estimates. The only event premise is the
literal deterministic coefficient box `|x j| ≤ M`. -/
theorem endpoint_periodicBesov_of_boundedCoefficients
    {d n : ℕ} (x : LayerIndex d n → ℝ) (M r : ℝ) (theta : ℝ≥0∞)
    (K : ℕ) (Lscalar Lprofile Czero CK : ℝ)
    (hM : 0 ≤ M) (hcoeff : ∀ j, |x j| ≤ M)
    (hr : 0 < r) (hK : Even K) (hKpos : 0 < K) (hrK : r < K)
    (hθ : 1 ≤ theta)
    (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hC0 : 0 ≤ Czero) (hCK : 0 ≤ CK)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ q : ℕ, 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv0 : ∀ y : ℝ, |iteratedDeriv 0 smoothAtom y| ≤ Czero)
    (hderivK : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ CK)
    (hbudget : if theta = ⊤ then ENNReal.ofReal
      (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) *
        (((1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
          ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))) *
            (1-ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))))⁻¹)^d) ≤ 1
      else ENNReal.ofReal (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) ^ theta.toReal *
      (((1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
          ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))) *
            (1-ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))))⁻¹)^d) ^ theta.toReal *
        Fintype.card (Shape d n) ≤ 1) :
    SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
      (periodicNativeSynthesisLinear x) := by
  classical
  let qlow : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(-r))
  let qhigh : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r)))
  let A : ℝ≥0∞ := ((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹)^d
  let B : ℝ≥0∞ := ENNReal.ofReal
    (M * (max (Lscalar*Czero) (Lprofile*CK))^d * (2:ℝ)^(r*(n:ℝ)))
  have hrK' : (r:ℝ) < (K:ℝ) := by exact_mod_cast hrK
  have hq : qlow < 1 ∧ qhigh < 1 := by
    simpa [qlow, qhigh] using ennreal_dyadic_profile_bases_lt_one hr hrK'
  have hA0 : A ≠ 0 := by
    have hpos : 0 < (1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹ := by
      have hfinite : 1-qlow ≠ ⊤ := by finiteness
      have hinv : 0 < (1-qlow)⁻¹ := ENNReal.inv_pos.mpr hfinite
      exact lt_of_lt_of_le hinv (le_add_of_nonneg_right (by positivity))
    dsimp [A]
    exact pow_ne_zero _ (ne_of_gt hpos)
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    have hlowden : 1-qlow ≠ 0 := ne_of_gt (tsub_pos_of_lt hq.1)
    have hhighden : 1-qhigh ≠ 0 := ne_of_gt (tsub_pos_of_lt hq.2)
    finiteness
  have hrow : ∀ t : Fin d → ℕ,
      (∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A := by
    intro t
    have h := endpoint_shape_profile_row_sum_le (n := n) t qlow qhigh hq.1 hq.2
    simpa [A] using h
  have hcol : ∀ s : Shape d n,
      (∑' t : Fin d → ℕ,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A := by
    intro s
    have h := endpoint_shape_profile_column_sum_le s.1 qlow qhigh hq.1 hq.2
    simpa [A] using h
  have hshape : ∀ s : Shape d n, ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (fixedShapeSynthesis (fun i => s.1 i)
          (fun j => x ⟨s,j⟩)) ≤
        B * nativeNikolskyShapeWeight t qlow qhigh s.1 := by
    intro s t
    have hsum : ∑ i : Fin d, s.1 i = n := by
      have hh := (Finset.mem_finsuppAntidiag'.mp s.2).1
      simpa [Finsupp.sum_fintype] using hh
    have hcoeff' : ∀ j : DyadicShapeCell d s.1, |x ⟨s,j⟩| ≤ M :=
      fun j => hcoeff ⟨s,j⟩
    simpa [B, qlow, qhigh] using
      (fixedShape_weightedBlockNorm_top_le_endpointProfile
        s.1 hsum t (fun j => x ⟨s,j⟩) M r Lscalar Lprofile Czero CK K
        hM hcoeff' hr.le hK hKpos hrK hLs hLp hC0 hCK
        hscalar hprofile hderiv0 hderivK)
  exact endpoint_periodicBesov_of_shapeProfile x r theta B A qlow qhigh hθ
    hA0 hAtop hrow hcol hshape (by simpa [A, B, qlow, qhigh] using hbudget)

/-- The arbitrary-b coefficient box defeats the existing smooth-grid
confinement event at the exact finite-layer covering threshold. -/
theorem endpoint_periodic_cover_obstruction_of_box_mass
    {d n k : ℕ} (hd : 0 < d) {b M A ε ρ : ℝ} (hb : 0 < b)
    (hM : 0 < M) (hA : 0 < A)
    (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρε : ρ ≤ A*ε)
    (K : Set (RealPeriodic d))
    (hclass : ∀ x ∈ coefficientBox (ι := LayerIndex d n) M,
      A • periodicNativeSynthesisLinear x ∈ K)
    (hscalarbox : ENNReal.ofReal (Real.exp (-b/4)) ≤
      ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-M) M))
    (hconf : (productStandardGaussian (LayerIndex d n)).real
      (smoothGoodUniformEvent d n ε) ≤
        Real.exp (-b * (Fintype.card (LayerIndex d n):ℝ)))
    (hgap : ((k-1:ℕ):ℝ) * Real.log 2 <
      (3/4) * b * (Fintype.card (LayerIndex d n):ℝ)) :
    ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber ⟨ρ,hρ⟩ K := by
  classical
  let μ := fun _ : LayerIndex d n => ProbabilityTheory.gaussianReal 0 1
  let E := coefficientBox (ι := LayerIndex d n) M
  let Q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-b * (Fintype.card (LayerIndex d n):ℝ)))
  have hbox := productMeasure_coefficientBox_exp_lower μ
    (by intro i; infer_instance) M b hb (by intro i; exact hscalarbox)
  have hmass : ((2^(k-1):ℕ):ℝ≥0∞) * Q <
      productStandardGaussian (LayerIndex d n) E := by
    have hexp : ((2:ℝ)^(k-1)) *
        Real.exp (-b*(Fintype.card (LayerIndex d n):ℝ)) <
        Real.exp (-b*(Fintype.card (LayerIndex d n):ℝ)/4) := by
      have htwo : (2:ℝ)^(k-1) =
          Real.exp (((k-1:ℕ):ℝ)*Real.log 2) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
        congr 1
        ring
      rw [htwo]
      rw [← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      nlinarith [hgap]
    have hnatcast : ((2^(k-1):ℕ):ℝ≥0∞) =
        ENNReal.ofReal ((2:ℝ)^(k-1)) := by
      norm_cast
    have hmul : ((2^(k-1):ℕ):ℝ≥0∞) * Q = ENNReal.ofReal
        (((2:ℝ)^(k-1)) *
          Real.exp (-b*(Fintype.card (LayerIndex d n):ℝ))) := by
      rw [hnatcast, show Q = ENNReal.ofReal
        (Real.exp (-b*(Fintype.card (LayerIndex d n):ℝ))) by rfl]
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hstrict : ((2^(k-1):ℕ):ℝ≥0∞) * Q <
        ENNReal.ofReal (Real.exp (-b*(Fintype.card (LayerIndex d n):ℝ)/4)) := by
      rw [hmul]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hexp
    exact hstrict.trans_le (by simpa [E, μ] using hbox)
  have hconfENN : productStandardGaussian (LayerIndex d n)
      (smoothGoodUniformEvent d n ε) ≤ Q := by
    have hc := ENNReal.ofReal_le_ofReal hconf
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hc
    simpa [Q] using hc
  exact periodicNative_externalCover_gt_of_class_mass hd hA hε hρ hρε
    K E Q hclass hconfENN hmass

/-- A single positive amplitude scale normalizes both the sup branch and every
finite `theta ≥ 1` branch; `N^(1/theta)` is the exact weak-composition factor. -/
noncomputable def endpointBesovScale (B H : ℝ) (N : ℕ) (p : ℝ) : ℝ :=
  (1 + B * H * (N:ℝ)^(1/p))⁻¹

theorem endpointBesovScale_pos {B H : ℝ} (hB : 0 < B) (hH : 0 < H)
    {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 0 ≤ p) :
    0 < endpointBesovScale B H N p := by
  unfold endpointBesovScale
  apply inv_pos.mpr
  have hNpow : 0 ≤ (N:ℝ)^(1/p) := Real.rpow_nonneg (by positivity) _
  linarith [mul_nonneg (mul_nonneg hB.le hH.le) hNpow]

theorem endpointBesovScale_times_mass_le_one {B H : ℝ} (hB : 0 < B)
    (hH : 0 < H) {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 0 ≤ p) :
    endpointBesovScale B H N p * B * H * (N:ℝ)^(1/p) ≤ 1 := by
  let Z := B * H * (N:ℝ)^(1/p)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hden : 0 < 1+Z := by linarith
  have hmul : endpointBesovScale B H N p * B * H * (N:ℝ)^(1/p) =
      (1+Z)⁻¹ * Z := by
    unfold endpointBesovScale
    dsimp [Z]
    ring
  rw [hmul]
  have hZle : Z ≤ 1+Z := by linarith
  calc
    (1+Z)⁻¹ * Z ≤ (1+Z)⁻¹ * (1+Z) :=
      mul_le_mul_of_nonneg_left hZle (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hden)

theorem endpointBesovScale_sup_budget {B H : ℝ} (hB : 0 < B)
    (hH : 0 < H) {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 0 ≤ p) :
    endpointBesovScale B H N p * B * H ≤ 1 := by
  have hNpow : 1 ≤ (N:ℝ)^(1/p) := by
    exact Real.one_le_rpow (by exact_mod_cast hN) (div_nonneg (by norm_num) hp)
  have h := endpointBesovScale_times_mass_le_one hB hH hN hp
  have hnonneg : 0 ≤ endpointBesovScale B H N p * B * H := by
    unfold endpointBesovScale
    positivity
  nlinarith

theorem endpointBesovScale_power_budget {B H : ℝ} (hB : 0 < B)
    (hH : 0 < H) {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (hp : 1 ≤ p) :
    (endpointBesovScale B H N p * B * H)^p * (N:ℝ) ≤ 1 := by
  have hscale := endpointBesovScale_times_mass_le_one hB hH hN (le_trans (by norm_num) hp)
  have hX : 0 ≤ (endpointBesovScale B H N p * B * H) * (N:ℝ)^(1/p) := by
    unfold endpointBesovScale
    positivity
  have hmass : 0 ≤ endpointBesovScale B H N p * B * H := by
    unfold endpointBesovScale
    positivity
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpow :
      ((endpointBesovScale B H N p * B * H) * (N:ℝ)^(1/p))^p ≤ 1 := by
    have h := Real.rpow_le_rpow hX hscale hp0
    simpa using h
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpoweq :
      ((endpointBesovScale B H N p * B * H) * (N:ℝ)^(1/p))^p =
        (endpointBesovScale B H N p * B * H)^p * (N:ℝ) := by
    rw [Real.mul_rpow hmass (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
    have he : (1/p)*p=1 := by field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hp)]
    rw [he, Real.rpow_one]
  rw [hpoweq] at hpow
  simpa only [Real.one_rpow] using hpow

/-- Convert the two-sided geometric mass to an ordinary real finite constant. -/
theorem endpoint_profileMassENNReal_eq_ofReal {d : ℕ} {r K : ℝ}
    (hr : 0 < r) (hKr : r < K) :
    (((1-ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
      ENNReal.ofReal ((2:ℝ)^(-(K-r))) *
        (1-ENNReal.ofReal ((2:ℝ)^(-(K-r))))⁻¹)^d) =
    ENNReal.ofReal (((1-(2:ℝ)^(-r))⁻¹ +
      (2:ℝ)^(-(K-r)) * (1-(2:ℝ)^(-(K-r)))⁻¹)^d) := by
  have hlow : (2:ℝ)^(-r) < 1 := by
    exact (real_dyadic_profile_bases_lt_one hr hKr).1
  have hhigh : (2:ℝ)^(-(K-r)) < 1 := by
    exact (real_dyadic_profile_bases_lt_one hr hKr).2
  have hlow0 : 0 ≤ (2:ℝ)^(-r) := by positivity
  have hhigh0 : 0 ≤ (2:ℝ)^(-(K-r)) := by positivity
  have hInvLow :
      (1-ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ =
        ENNReal.ofReal ((1-(2:ℝ)^(-r))⁻¹) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1:ℝ) hlow0,
      ← ENNReal.ofReal_inv_of_pos (by linarith)]
  have hInvHigh :
      (1-ENNReal.ofReal ((2:ℝ)^(-(K-r))))⁻¹ =
        ENNReal.ofReal ((1-(2:ℝ)^(-(K-r)))⁻¹) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1:ℝ) hhigh0,
      ← ENNReal.ofReal_inv_of_pos (by linarith)]
  rw [hInvLow, hInvHigh, ← ENNReal.ofReal_mul hhigh0,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_pow (by positivity)]

def EndpointProfileConstantsSpec (K : ℕ) (p : ℝ × ℝ × ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧
  (∀ q : ℕ, (∫ x : UnitAddCircle,
    ‖ScalarKernelL1.scalarBlockKernel q x‖ ∂AddCircle.haarAddCircle) ≤ p.1) ∧
  (∀ q : ℕ, 0 < q →
    (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
      ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * p.2.1) ∧
  (∀ y : ℝ, |iteratedDeriv 0 smoothAtom y| ≤ p.2.2.1) ∧
  (∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ p.2.2.2)

noncomputable def endpointProfileConstantTuple (K : ℕ) (hK : Even K) :
    ℝ × ℝ × ℝ × ℝ := Classical.choose (show ∃ p : ℝ × ℝ × ℝ × ℝ,
      EndpointProfileConstantsSpec K p from by
        obtain ⟨Ls,Lp,C0,CK,hLs,hLp,hC0,hCK,hs,hp,h0,hK'⟩ :=
          exists_endpoint_profile_constants hK
        exact ⟨(Ls,Lp,C0,CK), hLs,hLp,hC0,hCK,hs,hp,h0,hK'⟩)

theorem endpointProfileConstantTuple_spec (K : ℕ) (hK : Even K) :
    EndpointProfileConstantsSpec K (endpointProfileConstantTuple K hK) := by
  exact Classical.choose_spec (show ∃ p : ℝ × ℝ × ℝ × ℝ,
    EndpointProfileConstantsSpec K p from by
      obtain ⟨Ls,Lp,C0,CK,hLs,hLp,hC0,hCK,hs,hp,h0,hK'⟩ :=
        exists_endpoint_profile_constants hK
      exact ⟨(Ls,Lp,C0,CK), hLs,hLp,hC0,hCK,hs,hp,h0,hK'⟩)

noncomputable def endpointUniformBoxScaleConstant (d K : ℕ) (M r : ℝ)
    (hK : Even K) : ℝ :=
  let P := endpointProfileConstantTuple K hK
  let Lscalar := P.1+1
  let Lprofile := P.2.1+1
  let Czero := P.2.2.1+1
  let CKR := P.2.2.2+1
  let H := ((1-(2:ℝ)^(-r))⁻¹ +
    (2:ℝ)^(-((K:ℝ)-r))*(1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹)^d
  (1 + M * (max (Lscalar*Czero) (Lprofile*CKR))^d * H)⁻¹

/-- A coefficient box of any fixed finite amplitude can be scaled into the
literal periodic endpoint ball, with the theta-dependent `S_n^(1/theta)`
normalization proved explicitly. The smooth-kernel constants are instantiated
from their checked existential constructions. -/
theorem endpoint_scaled_box_synthesis_Besov
    {d n : ℕ} (hd : 2 ≤ d) (x : LayerIndex d n → ℝ)
    (M r : ℝ) (theta : ℝ≥0∞) (K : ℕ)
    (hM : 0 < M) (hcoeff : ∀ j, |x j| ≤ M)
    (hr : 0 < r) (hK : Even K) (hKpos : 0 < K) (hrK : r < K)
    (hθ : 1 ≤ theta) :
    ∃ amp : ℝ, 0 < amp ∧ amp ≤ 1 ∧
      amp • periodicNativeSynthesisLinear x ∈
        {f : RealPeriodic d | SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta f} ∧
      ∃ c : ℝ, c = endpointUniformBoxScaleConstant d K M r hK ∧ 0 < c ∧
        c * (2:ℝ)^(-r*(n:ℝ)) *
          (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) ≤ amp := by
  classical
  let P := endpointProfileConstantTuple K hK
  have hP := endpointProfileConstantTuple_spec K hK
  let Ls0 := P.1
  let Lp0 := P.2.1
  let C00 := P.2.2.1
  let CK0 := P.2.2.2
  have hLs0 := hP.1
  have hLp0 := hP.2.1
  have hC00 := hP.2.2.1
  have hCK0 := hP.2.2.2
  have hscalar0 := hP.2.2.2.2.1
  have hprofile0 := hP.2.2.2.2.2.1
  have hderiv0 := hP.2.2.2.2.2.2.1
  have hderivK0 := hP.2.2.2.2.2.2.2
  let Lscalar : ℝ := Ls0+1
  let Lprofile : ℝ := Lp0+1
  let Czero : ℝ := C00+1
  let CKR : ℝ := CK0+1
  have hLs : 0 < Lscalar := by dsimp [Lscalar]; linarith
  have hLp : 0 < Lprofile := by dsimp [Lprofile]; linarith
  have hC0 : 0 < Czero := by dsimp [Czero]; linarith
  have hCK : 0 < CKR := by dsimp [CKR]; linarith
  have hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar := by
    intro q
    have h := hscalar0 q
    dsimp [Lscalar]
    linarith
  have hprofile : ∀ q : ℕ, 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile := by
    intro q hq
    have h := hprofile0 q hq
    dsimp [Lprofile]
    calc
      _ ≤ ‖inverseProfileScale q K‖ * Lp0 := h
      _ ≤ ‖inverseProfileScale q K‖ * (Lp0+1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have hderiv0' : ∀ y : ℝ, |iteratedDeriv 0 smoothAtom y| ≤ Czero := by
    intro y
    have h := hderiv0 y
    dsimp [Czero]
    linarith
  have hderivK : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ CKR := by
    intro y
    have h := hderivK0 y
    dsimp [CKR]
    linarith
  let qlowR : ℝ := (2:ℝ)^(-r)
  let qhighR : ℝ := (2:ℝ)^(-((K:ℝ)-r))
  let Hreal : ℝ := ((1-qlowR)⁻¹ + qhighR*(1-qhighR)⁻¹)^d
  let N : ℕ := Fintype.card (Shape d n)
  let B0 : ℝ := M * (max (Lscalar*Czero) (Lprofile*CKR))^d *
    (2:ℝ)^(r*(n:ℝ))
  let amp : ℝ := endpointBesovScale B0 Hreal N theta.toReal
  have hrK' : (r:ℝ) < (K:ℝ) := by exact_mod_cast hrK
  have hlow : qlowR < 1 := by
    dsimp [qlowR]
    exact (real_dyadic_profile_bases_lt_one hr hrK').1
  have hhigh : qhighR < 1 := by
    dsimp [qhighR]
    exact (real_dyadic_profile_bases_lt_one hr hrK').2
  have hH : 0 < Hreal := by
    dsimp [Hreal]
    have hlow0 : 0 ≤ qlowR := by positivity
    have hhigh0 : 0 ≤ qhighR := by positivity
    have : 0 < 1-qlowR := by linarith
    have : 0 < 1-qhighR := by linarith
    positivity
  have hN : 1 ≤ N := by
    dsimp [N]
    rw [shape_card d n (by omega)]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hB0 : 0 < B0 := by
    dsimp [B0]
    have hD : 0 < max (Lscalar*Czero) (Lprofile*CKR) := by positivity
    positivity
  have hθp : 0 ≤ theta.toReal := ENNReal.toReal_nonneg
  have hamp : 0 < amp := by
    dsimp [amp]
    exact endpointBesovScale_pos hB0 hH hN hθp
  have hamp_le : amp ≤ 1 := by
    have hden : 1 ≤ 1+B0*Hreal*(N:ℝ)^(1/theta.toReal) := by
      have hp : 0 ≤ (N:ℝ)^(1/theta.toReal) := Real.rpow_nonneg (by positivity) _
      have hmul : 0 ≤ B0*Hreal*(N:ℝ)^(1/theta.toReal) := by positivity
      linarith
    dsimp [amp, endpointBesovScale]
    exact (inv_le_one₀ (by positivity)).2 hden
  have hXlower : 1 ≤ (2:ℝ)^(r*(n:ℝ)) * (N:ℝ)^(1/theta.toReal) := by
    have htwo : 1 ≤ (2:ℝ)^(r*(n:ℝ)) := by
      apply Real.one_le_rpow (by norm_num) (mul_nonneg hr.le (by positivity))
    have hNpow : 1 ≤ (N:ℝ)^(1/theta.toReal) := by
      apply Real.one_le_rpow (by exact_mod_cast hN)
        (div_nonneg (by norm_num) hθp)
    calc
      1 ≤ (2:ℝ)^(r*(n:ℝ)) := htwo
      _ = (2:ℝ)^(r*(n:ℝ)) * 1 := by ring
      _ ≤ (2:ℝ)^(r*(n:ℝ)) * (N:ℝ)^(1/theta.toReal) :=
        mul_le_mul_of_nonneg_left hNpow (by positivity)
  have hamp_lower :
      (1 + M * (max (Lscalar*Czero) (Lprofile*CKR))^d * Hreal)⁻¹ *
        (2:ℝ)^(-r*(n:ℝ)) * (N:ℝ)^(-(1/theta.toReal)) ≤ amp := by
    have hB : 0 < M * (max (Lscalar*Czero) (Lprofile*CKR))^d := by
      have hmax : 0 < max (Lscalar*Czero) (Lprofile*CKR) := by positivity
      positivity
    have hHpos : 0 < Hreal := hH
    have hX : 0 < (2:ℝ)^(r*(n:ℝ)) * (N:ℝ)^(1/theta.toReal) := by positivity
    have hden : 0 < 1 + B0*Hreal*(N:ℝ)^(1/theta.toReal) := by positivity
    have hbound :
        1 + B0*Hreal*(N:ℝ)^(1/theta.toReal) ≤
        (1+M*(max (Lscalar*Czero) (Lprofile*CKR))^d*Hreal)*
          ((2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal)) := by
      have hx := hXlower
      rw [show B0 = M*(max (Lscalar*Czero) (Lprofile*CKR))^d *
          (2:ℝ)^(r*(n:ℝ)) by rfl]
      nlinarith [mul_nonneg (mul_nonneg hB.le hHpos.le) (sub_nonneg.mpr hx)]
    have hinv := one_div_le_one_div_of_le hden hbound
    have heq :
        (1 + B0*Hreal*(N:ℝ)^(1/theta.toReal))⁻¹ = amp := by
      simp [amp, endpointBesovScale, B0, N]
    rw [← heq]
    have hpow :
        ((2:ℝ)^(r*(n:ℝ))*(N:ℝ)^(1/theta.toReal))⁻¹ =
          (2:ℝ)^(-r*(n:ℝ))*(N:ℝ)^(-(1/theta.toReal)) := by
      rw [mul_inv, ← Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)),
        ← Real.rpow_neg (by positivity : 0 ≤ (N:ℝ))]
      congr 2 <;> ring
    have hleft : ((1+M*(max (Lscalar*Czero) (Lprofile*CKR))^d*Hreal) *
        ((2:ℝ)^(r*(n:ℝ)) * (N:ℝ)^(1/theta.toReal)))⁻¹ =
        (1+M*(max (Lscalar*Czero) (Lprofile*CKR))^d*Hreal)⁻¹ *
          (2:ℝ)^(-r*(n:ℝ)) * (N:ℝ)^(-(1/theta.toReal)) := by
      rw [mul_inv, hpow]
      ring
    rw [← hleft]
    simpa [B0, one_div, mul_assoc, mul_left_comm, mul_comm] using hinv
  have hAmass :
      (((1-ENNReal.ofReal qlowR)⁻¹ +
        ENNReal.ofReal qhighR*(1-ENNReal.ofReal qhighR)⁻¹)^d) =
        ENNReal.ofReal Hreal := by
    simpa [qlowR, qhighR, Hreal] using
      endpoint_profileMassENNReal_eq_ofReal (d:=d) hr hrK'
  have hbudget : if theta = ⊤ then
      ENNReal.ofReal (amp*B0) * ENNReal.ofReal Hreal ≤ 1 else
      ENNReal.ofReal (amp*B0) ^ theta.toReal *
        ENNReal.ofReal Hreal ^ theta.toReal * (N:ℝ≥0∞) ≤ 1 := by
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hreal := endpointBesovScale_sup_budget hB0 hH hN hθp
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ amp*B0)]
      exact ENNReal.ofReal_le_one.mpr hreal
    · simp only [htop, ↓reduceIte]
      have hp : 1 ≤ theta.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).2 hθ
      have hreal := endpointBesovScale_power_budget hB0 hH hN hp
      have hconvert :
          ENNReal.ofReal (amp*B0)^theta.toReal *
            ENNReal.ofReal Hreal^theta.toReal * (N:ℝ≥0∞) =
          ENNReal.ofReal ((amp*B0*Hreal)^theta.toReal * (N:ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
          ENNReal.ofReal_rpow_of_nonneg hH.le (by linarith)]
        have hNcast : (N:ℝ≥0∞) = ENNReal.ofReal (N:ℝ) := by norm_cast
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (amp*B0)^theta.toReal),
          hNcast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (by positivity) hH.le]
      rw [hconvert]
      exact ENNReal.ofReal_le_one.mpr hreal
  have hscaled : ∀ j, |(amp • x) j| ≤ amp*M := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hamp]
    exact mul_le_mul_of_nonneg_left (hcoeff j) hamp.le
  have hbudgetScaled : if theta = ⊤ then
      ENNReal.ofReal (amp * M * (max (Lscalar*Czero) (Lprofile*CKR))^d *
        (2:ℝ)^(r*(n:ℝ))) * (((1-ENNReal.ofReal qlowR)⁻¹ +
        ENNReal.ofReal qhighR*(1-ENNReal.ofReal qhighR)⁻¹)^d) ≤ 1
      else
        ENNReal.ofReal (amp * M * (max (Lscalar*Czero) (Lprofile*CKR))^d *
          (2:ℝ)^(r*(n:ℝ)))^theta.toReal * (((1-ENNReal.ofReal qlowR)⁻¹ +
          ENNReal.ofReal qhighR*(1-ENNReal.ofReal qhighR)⁻¹)^d)^theta.toReal *
          (N:ℝ≥0∞) ≤ 1 := by
    have hcoef' : amp * M * (max (Lscalar*Czero) (Lprofile*CKR))^d *
        (2:ℝ)^(r*(n:ℝ)) = amp*B0 := by
      dsimp [B0]
      ring
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hb := hbudget
      simp only [htop, ↓reduceIte] at hb
      rw [hAmass, hcoef']
      exact hb
    · simp only [htop, ↓reduceIte]
      have hb := hbudget
      simp only [htop, ↓reduceIte] at hb
      rw [hAmass, hcoef']
      exact hb
  have hclass := endpoint_periodicBesov_of_boundedCoefficients
    (fun j => amp*x j) (amp*M) r theta K Lscalar Lprofile Czero CKR
    (mul_nonneg hamp.le hM.le) hscaled
    hr hK hKpos hrK hθ hLs.le hLp.le hC0.le hCK.le
    hscalar hprofile hderiv0' hderivK
    (by simpa [N, qlowR, qhighR] using hbudgetScaled)
  refine ⟨amp,hamp,hamp_le,?_,?_⟩
  · have hmap : periodicNativeSynthesisLinear (fun j => amp*x j) =
        amp • periodicNativeSynthesisLinear x := by
      exact (periodicNativeSynthesisLinear (d:=d) (n:=n)).map_smul amp x
    change SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
      (amp • periodicNativeSynthesisLinear x)
    rw [← hmap]
    exact hclass
  · refine ⟨(1 + M * (max (Lscalar*Czero) (Lprofile*CKR))^d * Hreal)⁻¹,
      ?_, ?_, hamp_lower⟩
    · dsimp [endpointUniformBoxScaleConstant, P, Lscalar, Lprofile,
        Czero, CKR, Hreal, qlowR, qhighR]
    · positivity

/-- The literal Besov ball is balanced under positive contractions, in both
the finite-sum and supremum (`theta=∞`) definitions. -/
theorem endpoint_besovUnitBall_smul_contraction {d : ℕ}
    (p : ℝ≥0∞) (r : ℝ) (theta : ℝ≥0∞) (f : RealPeriodic d)
    {a : ℝ} (ha : 0 < a) (haone : a ≤ 1)
    (hf : SmoothResolution.BesovUnitBall p r theta f) :
    SmoothResolution.BesovUnitBall p r theta (a • f) := by
  classical
  by_cases htop : theta = ⊤
  · simp only [SmoothResolution.BesovUnitBall, htop, ↓reduceIte] at hf ⊢
    intro s
    rw [weightedBlockNorm_smul ha]
    have hco : ENNReal.ofReal a ≤ 1 := ENNReal.ofReal_le_one.mpr haone
    calc
      ENNReal.ofReal a * SmoothResolution.weightedBlockNorm p r s f ≤
          1 * 1 := mul_le_mul hco (hf s) bot_le bot_le
      _ = 1 := by simp
  · have hp : 0 ≤ theta.toReal := ENNReal.toReal_nonneg
    have hpow : a ^ theta.toReal ≤ 1 :=
      Real.rpow_le_one ha.le haone hp
    have henergy : smoothBesovEnergy p r theta f ≤ 1 :=
      (smoothBesovUnitBall_iff_energy_le_one p r htop f).mp hf
    rw [smoothBesovUnitBall_iff_energy_le_one p r htop]
    rw [smoothBesovEnergy_smul ha]
    have hco : ENNReal.ofReal (a ^ theta.toReal) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr hpow
    calc
      ENNReal.ofReal (a ^ theta.toReal) *
          smoothBesovEnergy p r theta f ≤ 1 * 1 :=
        mul_le_mul hco henergy bot_le bot_le
      _ = 1 := by simp

set_option maxHeartbeats 20000000 in
/-- The fixed profile constants give one uniform synthesis scale for every
grade. The coefficient box can therefore be placed inside the same literal
Besov class at all grades, including the Nikolsky endpoint. -/
theorem endpoint_uniform_scaled_box_Besov
    {d : ℕ} (hd : 2 ≤ d) (M r : ℝ) (theta : ℝ≥0∞) (K : ℕ)
    (hM : 0 < M) (hr : 0 < r) (hK : Even K) (hKpos : 0 < K)
    (hrK : r < K) (hθ : 1 ≤ theta) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, ∀ x : LayerIndex d n → ℝ,
      (∀ j, |x j| ≤ M) →
      SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
        ((a * periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
          periodicNativeSynthesisLinear x) := by
  classical
  let a := endpointUniformBoxScaleConstant d K M r hK / 2
  have hconstant : 0 < endpointUniformBoxScaleConstant d K M r hK := by
    have hP := endpointProfileConstantTuple_spec K hK
    dsimp [EndpointProfileConstantsSpec] at hP
    have h1 : 0 < (endpointProfileConstantTuple K hK).1+1 := by
      have hh := hP.1
      linarith
    have h2 : 0 < (endpointProfileConstantTuple K hK).2.1+1 := by
      have hh := hP.2.1
      linarith
    have h3 : 0 < (endpointProfileConstantTuple K hK).2.2.1+1 := by
      have hh := hP.2.2.1
      linarith
    have h4 : 0 < (endpointProfileConstantTuple K hK).2.2.2+1 := by
      have hh := hP.2.2.2
      linarith
    have hmax : 0 < max (((endpointProfileConstantTuple K hK).1+1) *
        ((endpointProfileConstantTuple K hK).2.2.1+1))
      (((endpointProfileConstantTuple K hK).2.1+1) *
        ((endpointProfileConstantTuple K hK).2.2.2+1)) :=
      lt_of_lt_of_le (mul_pos h1 h3) (le_max_left _ _)
    have hrK' : r < (K:ℝ) := by exact_mod_cast hrK
    have hbaseLow : (2:ℝ)^(-r) < 1 :=
      (real_dyadic_profile_bases_lt_one hr hrK').1
    have hbaseHigh : (2:ℝ)^(-((K:ℝ)-r)) < 1 :=
      (real_dyadic_profile_bases_lt_one hr hrK').2
    have hdenLow : 0 < 1-(2:ℝ)^(-r) := by linarith
    have hdenHigh : 0 < 1-(2:ℝ)^(-((K:ℝ)-r)) := by linarith
    have hmass : 0 < (1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-((K:ℝ)-r)) *
        (1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹ := by positivity
    have hpow : 0 < ((1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-((K:ℝ)-r)) *
        (1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹)^d := by positivity
    have hbase : 0 < 1 + M * max (((endpointProfileConstantTuple K hK).1+1) *
        ((endpointProfileConstantTuple K hK).2.2.1+1))
      (((endpointProfileConstantTuple K hK).2.1+1) *
        ((endpointProfileConstantTuple K hK).2.2.2+1)) ^ d *
      ((1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-((K:ℝ)-r)) *
        (1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹)^d := by
      have hfactor : 0 ≤ M * max (((endpointProfileConstantTuple K hK).1+1) *
          ((endpointProfileConstantTuple K hK).2.2.1+1))
        (((endpointProfileConstantTuple K hK).2.1+1) *
          ((endpointProfileConstantTuple K hK).2.2.2+1))^d *
        ((1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-((K:ℝ)-r)) *
          (1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹)^d := by positivity
      linarith
    change 0 < (1 + M * max (((endpointProfileConstantTuple K hK).1+1) *
        ((endpointProfileConstantTuple K hK).2.2.1+1))
      (((endpointProfileConstantTuple K hK).2.1+1) *
        ((endpointProfileConstantTuple K hK).2.2.2+1)) ^ d *
      ((1-(2:ℝ)^(-r))⁻¹ + (2:ℝ)^(-((K:ℝ)-r)) *
        (1-(2:ℝ)^(-((K:ℝ)-r)))⁻¹)^d)⁻¹
    exact inv_pos.mpr hbase
  have ha : 0 < a := by dsimp [a]; exact div_pos hconstant (by norm_num)
  refine ⟨a,ha,?_⟩
  intro n x hcoeff
  obtain ⟨amp,hamp,hamp_le,hf,c,hceq,hc,hscale⟩ :=
    endpoint_scaled_box_synthesis_Besov hd x M r theta K hM hcoeff
      hr hK hKpos hrK hθ
  have hcard : (Fintype.card (Shape d n):ℝ) = hyperbolicCount d n := by
    rw [shape_card d n (by omega)]
    rfl
  have hexp : (1/2-1/theta.toReal)-1/2 = -(1/theta.toReal) := by ring
  have hscaleEq : periodicSynthesisScale d n r (1/2-1/theta.toReal) =
      (2:ℝ)^(-r*(n:ℝ)) *
        (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) := by
    unfold periodicSynthesisScale
    rw [hexp]
    rw [hcard]
  have hfactor : (c/2) *
      ((2:ℝ)^(-r*(n:ℝ)) *
        (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal))) ≤
      c * (2:ℝ)^(-r*(n:ℝ)) *
        (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) := by
    have hnonneg : 0 ≤ (2:ℝ)^(-r*(n:ℝ)) *
        (Fintype.card (Shape d n):ℝ)^(-(1/theta.toReal)) := by positivity
    nlinarith [mul_nonneg hnonneg hc.le]
  have haeq : a = c/2 := by
    dsimp [a]
    rw [hceq]
  have htarget :
      a * periodicSynthesisScale d n r (1/2-1/theta.toReal) ≤ amp := by
    rw [haeq, hscaleEq]
    exact hfactor.trans hscale
  have htargetpos : 0 <
      a * periodicSynthesisScale d n r (1/2-1/theta.toReal) :=
    mul_pos ha (periodicSynthesisScale_pos (by omega) _ _)
  have hratio : 0 <
      (a * periodicSynthesisScale d n r (1/2-1/theta.toReal))/amp :=
    div_pos htargetpos hamp
  have hratioone :
      (a * periodicSynthesisScale d n r (1/2-1/theta.toReal))/amp ≤ 1 :=
    (div_le_one hamp).2 htarget
  have hcontract := endpoint_besovUnitBall_smul_contraction
    (⊤ : ℝ≥0∞) r theta (amp • periodicNativeSynthesisLinear x)
    hratio hratioone hf
  have hcompose :
      ((a * periodicSynthesisScale d n r (1/2-1/theta.toReal))/amp) •
        (amp • periodicNativeSynthesisLinear x) =
      (a * periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
        periodicNativeSynthesisLinear x := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [← hcompose]
  exact hcontract

/-- For every positive exponential cost, a sufficiently wide Gaussian
coefficient box lies at a fixed (cost-dependent) periodic scale inside the
literal p=∞ Besov class, uniformly over every grade. -/
theorem endpoint_besov_box_mass_for_every_exponent
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (theta : ℝ≥0∞) (K : ℕ)
    (hr : 0 < r) (hK : Even K) (hKpos : 0 < K)
    (hrK : r < K) (hθ : 1 ≤ theta) :
    ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
            periodicNativeSynthesisLinear x ∈
              {f : RealPeriodic d | SmoothResolution.BesovUnitBall
                (⊤ : ℝ≥0∞) r theta f}} := by
  intro δ hδ
  obtain ⟨M,hM,hscalar⟩ := exists_standardGaussian_box_for_exponent
    (b := 4*δ) (by positivity)
  obtain ⟨a,ha,hinside⟩ := endpoint_uniform_scaled_box_Besov
    hd M r theta K hM hr hK hKpos hrK hθ
  refine ⟨a,ha,0,?_⟩
  intro n hn
  let μ : LayerIndex d n → Measure ℝ := fun _ => ProbabilityTheory.gaussianReal 0 1
  have hbox := productMeasure_coefficientBox_exp_lower μ
    (by intro i; infer_instance) M (4*δ) (by positivity)
    (by intro i; simpa using hscalar)
  have hdim : (Fintype.card (LayerIndex d n):ℝ) = nativeDimension d n := by
    rw [layerIndex_card d n (by omega), nativeDimension, hyperbolicCount]
    push_cast
    ring
  have hexp : -(4*δ)*(Fintype.card (LayerIndex d n):ℝ)/4 =
      -δ*nativeDimension d n := by rw [← hdim]; ring
  have hbox' : ENNReal.ofReal (Real.exp (-δ*nativeDimension d n)) ≤
      productStandardGaussian (LayerIndex d n) (coefficientBox M) := by
    have hh := hbox
    rw [hexp] at hh
    simpa [μ, productStandardGaussian] using hh
  have hsub : coefficientBox (ι := LayerIndex d n) M ⊆
      {x | (a*periodicSynthesisScale d n r (1/2-1/theta.toReal)) •
        periodicNativeSynthesisLinear x ∈
          {f : RealPeriodic d | SmoothResolution.BesovUnitBall
            (⊤ : ℝ≥0∞) r theta f}} := by
    intro x hx
    apply hinside n x
    intro j
    have hj := hx j
    exact abs_le.mpr (by simpa [Set.mem_Icc] using hj)
  exact hbox'.trans (measure_mono hsub)

/-- The endpoint's actual full-coordinate box mass and sampled synthesis
identity feed the compact-domain entropy extraction, for every theta≥1. -/
theorem endpoint_periodic_besov_entropy_rate
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (theta : ℝ≥0∞)
    (hr : 0 < r) (hθ : 1 ≤ theta) (K : ℕ) (hK : Even K)
    (hKpos : 0 < K) (hrK : r < K) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/theta.toReal)*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | SmoothResolution.BesovUnitBall
              (⊤ : ℝ≥0∞) r theta f} := by
  let beta : ℝ := 1/2-1/theta.toReal
  let classSet : Set (RealPeriodic d) :=
    {f | SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta f}
  have hclass := endpoint_besov_box_mass_for_every_exponent
    hd r theta K hr hK hKpos hrK hθ
  have hrate := AlignmentExponentialBoxEntropy.entropy_rate_of_exponentially_large_native_class_mass
    (α := UnitAddTorus (Fin d)) (d:=d) hd classSet r beta hr
    (fun n => periodicNativeSynthesisLinear (d:=d) (n:=n))
    (fun n q => periodicMidpoint (q.val))
    (by
      intro n x q
      rw [periodicNativeSynthesisLinear_apply,
        smoothPeriodicSynthesis_midpoint_eq])
    hclass
  simpa [beta, classSet] using hrate

/-- The top-`theta` specialization is the periodic Nikolsky entropy endpoint.
The equality is definitional through the manuscript's Nikolsky alias. -/
theorem endpoint_periodic_nikolsky_entropy_rate
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ)
    (hr : 0 < r) (K : ℕ) (hK : Even K)
    (hKpos : 0 < K) (hrK : r < K) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        ((r+1/2)*((d-1:ℕ):ℝ)+1/2)) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | SmoothResolution.NikolskyUnitBall
              (⊤ : ℝ≥0∞) r f} := by
  have h := endpoint_periodic_besov_entropy_rate hd r ⊤ hr le_top K hK
    hKpos hrK
  have htopreal : (⊤:ℝ≥0∞).toReal = 0 := by simp
  rcases h with ⟨c,hc,k₀,hk₀,hk⟩
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk₀k
  have hbound := hk k hk₀k
  have hexp : r*((d-1:ℕ):ℝ) +
      (1/2+(1/2-1/(⊤:ℝ≥0∞).toReal)*((d-1:ℕ):ℝ)) =
        (r+1/2)*((d-1:ℕ):ℝ)+1/2 := by simp [htopreal]; ring
  simp [htopreal] at hbound
  have hexp' : r*((d-1:ℕ):ℝ) +
      (1/2+(1/2)*((d-1:ℕ):ℝ)) =
        (r+1/2)*((d-1:ℕ):ℝ)+1/2 := by ring
  change ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
      ((r+1/2)*((d-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | SmoothResolution.BesovUnitBall
            (⊤ : ℝ≥0∞) r (⊤ : ℝ≥0∞) f}
  rw [← hexp']
  norm_num at hbound
  exact hbound

end BrownianSharp
