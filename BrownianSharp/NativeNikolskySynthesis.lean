import BrownianSharp.PeriodicNativeCover
import BrownianSharp.FixedShapeBlockConvolution
import BrownianSharp.FixedShapeBlockLp
import BrownianSharp.SmoothCoefficientEvents
import BrownianSharp.UnitTorusMeasure
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.PeriodicAtomDerivatives
import BrownianSharp.NativeLayerThetaBudget
import Mathlib.Tactic

/-! Exact finite decomposition of the native synthesis by weak-composition
shape, together with the coefficient budget supplied by the joint good event.
The point of this module is to preserve the coordinatewise shape scales for
the later Nikolsky summation. -/

noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockVariance

/-- The normalization in the inverse-derivative symbol contributes at most
the expected dyadic inverse scale; the `2π` factor only improves the bound. -/
theorem inverseProfileScale_norm_le_dyadic (t K : ℕ) :
    ‖inverseProfileScale t K‖ ≤ (((2 : ℝ) ^ t)⁻¹) ^ K := by
  unfold inverseProfileScale
  rw [norm_pow]
  have hb : 1 ≤ ‖(2 * Real.pi * Complex.I : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I]
    norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hbase :
      ‖((2 : ℝ) ^ t : ℂ)⁻¹ / (2 * Real.pi * Complex.I)‖ ≤
        ((2 : ℝ) ^ t)⁻¹ := by
    rw [norm_div]
    have hreal : ‖((2 : ℝ) ^ t : ℂ)‖ = (2 : ℝ) ^ t := by
      simp [norm_pow]
    have hnum : ‖((2 : ℝ) ^ t : ℂ)⁻¹‖ = ((2 : ℝ) ^ t)⁻¹ := by
      rw [norm_inv, hreal]
    rw [hnum]
    have hp : 0 ≤ ((2 : ℝ) ^ t)⁻¹ := by positivity
    apply (div_le_iff₀ (by positivity : 0 < ‖(2 * Real.pi * Complex.I : ℂ)‖)).2
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hb)]
  have hn : 0 ≤ ‖((2 : ℝ) ^ t : ℂ)⁻¹ / (2 * Real.pi * Complex.I)‖ := norm_nonneg _
  have ht : 0 ≤ ((2 : ℝ) ^ t)⁻¹ := by positivity
  exact pow_le_pow_left₀ hn hbase K

private theorem periodicNativeAtom_apply_eq_dyadicShapeAtom {d n : ℕ}
    (r : Shape d n) (j : DyadicShapeCell d r.1) :
    ∀ x, periodicNativeAtom (⟨r, j⟩ : LayerIndex d n) x =
      dyadicShapeAtom r.1 j x := by
  intro x
  change (∏ i : Fin d, PeriodicCover.periodizedDyadicAtom1
      (layerIndexDepth (⟨r, j⟩ : LayerIndex d n) i)
      (layerIndexCell (⟨r, j⟩ : LayerIndex d n) i)
      (layerIndexCell_lt (⟨r, j⟩ : LayerIndex d n) i) (x i)) = _
  simp only [layerIndexDepth, layerIndexCell]
  simp only [dyadicShapeAtom]
  apply Finset.prod_congr rfl
  intro i hi
  exact (congrArg (fun f : C(UnitAddCircle, ℝ) => f (x i))
    (periodizedDyadicAtomDerivative1_zero_eq_existing
      (r.1 i) (j i).val (j i).isLt)).symm

/-- The actual native sum is the finite sum of its fixed-shape syntheses.
This is an equality of continuous periodic functions, not only of midpoint
samples. -/
theorem periodicNativeSynthesisLinear_eq_sum_shapes {d n : ℕ}
    (x : LayerIndex d n → ℝ) :
    periodicNativeSynthesisLinear x =
      ∑ r : Shape d n,
        fixedShapeSynthesis (fun i => r.1 i)
          (fun j => x ⟨r, j⟩) := by
  classical
  apply ContinuousMap.ext
  intro z
  change (∑ a : LayerIndex d n, x a • periodicNativeAtom a) z =
    (∑ r : Shape d n, fixedShapeSynthesis (fun i => r.1 i)
      (fun j => x ⟨r, j⟩)) z
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [fixedShapeSynthesis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [periodicNativeAtom_apply_eq_dyadicShapeAtom]
  simp [dyadicShapeDerivativeAtom, dyadicShapeAtom]

/-- The normalized `Lᵖ` block norm of the native sum is at most the sum of the
fixed-shape block norms. The multiplier block is a proved linear operator, so
this is a genuine finite Minkowski step over shapes. -/
theorem periodicNative_weightedBlockNorm_le_sum_shapes {d n : ℕ}
    (p : ℝ) (hp : 1 ≤ p) (r : ℝ) (t : Fin d → ℕ)
    (x : LayerIndex d n → ℝ) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
        (periodicNativeSynthesisLinear x) ≤
      ∑ a : Shape d n, SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
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
  have hpenn : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact hp
  unfold SmoothResolution.weightedBlockNorm
  rw [show (fun z : UnitAddTorus (Fin d) =>
      SmoothResolution.block t (periodicNativeSynthesisLinear x) z) =
      (fun z => ∑ a : Shape d n, SmoothResolution.block t
        (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) from by
          funext z
          exact hdecomp z]
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ))) *
        ∑ a : Shape d n,
          eLpNorm (fun z => SmoothResolution.block t
            (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
            (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
          have htri := MeasureTheory.eLpNorm_sum_le
            (μ := (volume : Measure (UnitAddTorus (Fin d))))
            (p := ENNReal.ofReal p)
            (f := fun a : Shape d n => fun z : UnitAddTorus (Fin d) =>
              SmoothResolution.block t
                (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
            (s := (Finset.univ : Finset (Shape d n))) hpenn
          have htri' : eLpNorm (fun z : UnitAddTorus (Fin d) =>
              ∑ a : Shape d n, SmoothResolution.block t
                (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
              (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) ≤
              ∑ a : Shape d n, eLpNorm (fun z => SmoothResolution.block t
                (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
                (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
            have hsumfun :
                (∑ a : Shape d n, fun z : UnitAddTorus (Fin d) =>
                  SmoothResolution.block t
                    (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) =
                (fun z => ∑ a : Shape d n, SmoothResolution.block t
                  (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z) := by
              funext z
              simp
            rw [← hsumfun]
            simpa only [Finset.sum_attach] using htri
          exact mul_le_mul_of_nonneg_left
            htri' bot_le
    _ = ∑ a : Shape d n,
          ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ))) *
            eLpNorm (fun z => SmoothResolution.block t
              (fixedShapeSynthesis (fun i => a.1 i) (fun j => x ⟨a,j⟩)) z)
              (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
          rw [Finset.mul_sum]

/-- On the simultaneous coefficient event, every shape has the explicit
finite-p budget `Σ_j |x_{r,j}|^p ≤ 2·2^n(1+M_p)`. -/
theorem smoothShapeCoefficientEnergy_le_on_joint_event {d n : ℕ}
    (p : ℝ) (hp : 0 < p) {x : LayerIndex d n → ℝ}
    (hx : x ∈ smoothShapeJointGoodEvent p Finset.univ)
    (r : Shape d n) :
    smoothShapeCoefficientEnergy r p x ≤
      2 * (2 : ℝ) ^ n * (1 + gaussianAbsoluteMoment p) := by
  have hr : r ∈ (Finset.univ : Finset (Shape d n)) := Finset.mem_univ r
  unfold smoothShapeJointGoodEvent at hx
  have h' := hx r hr
  unfold smoothShapeCoefficientBudget at h'
  have hcard : (Fintype.card (SmoothShapeCells r) : ℝ) = (2 : ℝ) ^ n := by
    simp [SmoothShapeCells, Fintype.card_pi]
    have hg : (∑ i : Fin d, r.1 i) = n := by
      have hh := (Finset.mem_finsuppAntidiag'.mp r.2).1
      simpa [Finsupp.sum_fintype] using hh
    rw [Finset.prod_pow_eq_pow_sum, hg]
  rw [hcard] at h'
  nlinarith

private theorem shape_product_sum_le_pi_tsum {d n : ℕ}
    (f : Fin d → ℕ → ℝ≥0∞) :
    (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) ≤
      ∏ i : Fin d, ∑' s : ℕ, f i s := by
  classical
  have hsum : (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) =
      ∑' a : Shape d n, ∏ i : Fin d, f i (a.1 i) := by
    symm
    exact tsum_fintype (L := .unconditional _) _
  rw [hsum]
  calc
    _ ≤ ∑' s : Fin d → ℕ, ∏ i : Fin d, f i (s i) := by
      let e : Shape d n → (Fin d → ℕ) := fun a i => a.1 i
      have he : Function.Injective e := by
        intro a b hab
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        exact congrFun hab i
      exact ENNReal.tsum_comp_le_tsum_of_injective he
        (fun s => ∏ i : Fin d, f i (s i))
    _ = ∏ i : Fin d, ∑' s : ℕ, f i s :=
      BrownianSharp.NativeLayerThetaBudget.ennreal_tsum_pi_prod d f

/-- The sum over grade-`n` source shapes of a two-sided coordinatewise
geometric profile is bounded by the product of its one-coordinate series.
The grade restriction is handled by injection into all depth profiles, so no
weak-composition factor is paid. -/
theorem shape_twoSided_geometric_sum_le {d n : ℕ}
    (t : Fin d → ℕ) (qlow qhigh : ℝ≥0∞)
    (hqlow : qlow < 1) (hqhigh : qhigh < 1) :
    (∑ a : Shape d n, ∏ i : Fin d,
      if t i ≤ a.1 i then qlow ^ (a.1 i - t i)
      else qhigh ^ (t i - a.1 i)) ≤
      ((1 - qlow)⁻¹ + qhigh * (1 - qhigh)⁻¹) ^ d := by
  let f : Fin d → ℕ → ℝ≥0∞ := fun i s =>
    if t i ≤ s then qlow ^ (s-t i) else qhigh ^ (t i-s)
  have hcoord : ∀ i : Fin d,
      (∑' s : ℕ, f i s) ≤ (1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹ := by
    intro i
    have h := BrownianSharp.NativeLayerThetaBudget.reverseTsum_le_of_pointwise_split
      (t i) qlow qhigh 1 1 hqlow hqhigh (f i)
      (by intro s hs; simp [f, hs])
      (by intro s hs; simp [f, Nat.not_le_of_gt hs])
    simpa using h
  have hprod : (∏ i : Fin d, ∑' s : ℕ, f i s) ≤
      ((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹) ^ d := by
    calc
      _ ≤ ∏ _i : Fin d, ((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹) := by
        exact Finset.prod_le_prod (fun i hi => hcoord i)
      _ = _ := by simp
  have hbase := shape_product_sum_le_pi_tsum (n := n) f
  calc
    _ = ∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [f]
    _ ≤ ∏ i : Fin d, ∑' s : ℕ, f i s := hbase
    _ ≤ _ := hprod

/-- Coordinatewise fixed-shape decay for the actual smooth block. High output
coordinates are inverted by an even-order derivative; low coordinates retain
the uniform scalar-block kernel. Every constant is supplied by an already
proved compact-profile or bump-derivative estimate. -/
theorem fixedShapeBlock_nativeDecay_integral {d : ℕ}
    (s t : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 1 ≤ p) (K : ℕ) (hK : Even K) (hKpos : 0 < K)
    (Lscalar Lprofile Cderiv : ℝ)
    (hLscalar : 0 ≤ Lscalar) (hLprofile : 0 ≤ Lprofile)
    (hCderiv : 0 ≤ Cderiv)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ (q : ℕ), 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤
          ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ Cderiv) :
    (∫ x : UnitAddTorus (Fin d), ‖SmoothResolution.block t
        (fixedShapeSynthesis s c) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, if s i < t i then
        ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar) ^ p *
      (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ *
        ((if s i < t i then Cderiv else 1) *
          (2 : ℝ) ^ (s i * (if s i < t i then K else 0))) ^ p) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  let k : Fin d → ℕ := fun i => if s i < t i then K else 0
  let Linv : Fin d → ℝ := fun i =>
    if s i < t i then ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar
  let C : Fin d → ℝ := fun i => if s i < t i then Cderiv else 1
  have hKne : K ≠ 0 := by omega
  have hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)) := by
    intro i
    dsimp [k]
    split_ifs with h
    · right
      exact ⟨by omega, hKpos, hK⟩
    · exact Or.inl rfl
  have hLinv : ∀ i, 0 ≤ Linv i := by
    intro i
    dsimp [Linv]
    split_ifs
    · exact mul_nonneg (norm_nonneg _) hLprofile
    · exact hLscalar
  have hhigh : ∀ i, k i ≠ 0 →
      0 < t i ∧ Even (k i) ∧
        (∫ x : UnitAddCircle, ‖inverseMultiplierKernel (t i) (k i) x‖
          ∂AddCircle.haarAddCircle) ≤ Linv i := by
    intro i hk
    have hsi : s i < t i := by
      by_contra h
      have : k i = 0 := by simp [k, not_lt.mp h]
      exact hk this
    have ht : 0 < t i := by omega
    have hkK : k i = K := by simp [k, hsi]
    refine ⟨ht, ?_, ?_⟩
    · simpa [hkK] using hK
    · simpa [Linv, hsi, hkK] using hprofile (t i) ht
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    dsimp [C]
    split_ifs <;> positivity
  have hderiv' : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i := by
    intro i y
    by_cases hsi : s i < t i
    · simp [k, C, hsi]
      exact hderiv y
    · simp [k, C, hsi, smoothAtom_abs_le_one]
  have hmain := fixedShapeBlock_rpow_integral_le_general s t k c p hp
    hscale Lscalar hLscalar hscalar Linv hLinv hhigh C hC hderiv'
  have hkernel :
      (∏ i : Fin d, if k i = 0 then Lscalar else Linv i) =
        ∏ i : Fin d, if s i < t i then
          ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hst : s i < t i
    · simp [k, Linv, hst, hKne]
    · simp [k, Linv, hst]
  rw [hkernel] at hmain
  simpa [k, C] using hmain

/-- All constants in the fixed-shape decay estimate can be chosen from the
actual compact smooth profiles, uniformly over every shape, coefficient
vector, and output block. -/
theorem exists_fixedShapeBlock_nativeDecay_constants {K : ℕ}
    (hK : Even K) (hKpos : 0 < K) :
    ∃ Lscalar Lprofile Cderiv : ℝ,
      0 ≤ Lscalar ∧ 0 ≤ Lprofile ∧ 0 ≤ Cderiv ∧
      (∀ q : ℕ,
        (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
          ∂AddCircle.haarAddCircle) ≤ Lscalar) ∧
      (∀ (q : ℕ), 0 < q →
        (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
          ∂AddCircle.haarAddCircle) ≤
            ‖inverseProfileScale q K‖ * Lprofile) ∧
      (∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ Cderiv) := by
  obtain ⟨Lscalar, hLscalar, hscalar⟩ := exists_scalarBlockKernel_uniform_L1_bound
  obtain ⟨Lprofile, hLprofile, hprofile⟩ :=
    exists_inverseMultiplierKernel_uniform_L1_bound hK
  obtain ⟨Cderiv, hCderiv, hderiv⟩ := exists_smoothAtom_iteratedDeriv_bound K
  refine ⟨Lscalar, Lprofile, Cderiv, hLscalar, hLprofile, hCderiv.le,
    hscalar, ?_, hderiv⟩
  intro q hq
  exact hprofile q hq

end BrownianSharp
