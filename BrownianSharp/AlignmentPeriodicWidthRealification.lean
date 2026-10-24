import BrownianSharp.AlignmentPeriodicReconstruction
import BrownianSharp.AlignmentTrigonometricL2
import BrownianSharp.FiniteCoordinateLayers
import BrownianSharp.AlignmentPeriodicRealEnergy
import BrownianSharp.UnitTorusMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Real coordinate bridge for complex finite Fourier features. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentPeriodicWidthRealification
open BrownianSharp
open BrownianSharp.Torus BrownianSharp.SmoothResolution UnitAddTorus BrownianSharp.AlignmentPeriodicRealEnergy

def complexSourceCoord (z : ℂ) (b : Fin 2) : ℝ :=
  if b.val = 0 then z.re else z.im

def complexFeatureCoord (z : ℂ) (b : Fin 2) : ℝ :=
  if b.val = 0 then z.re else -z.im

theorem complex_pair_dot (z w : ℂ) :
    (∑ b : Fin 2, complexSourceCoord z b * complexFeatureCoord w b) =
      (z*w).re := by
  rw [Fin.sum_univ_succ]
  simp [complexSourceCoord, complexFeatureCoord, Complex.mul_re]
  <;> ring

theorem complex_feature_pair_norm_sq (z : ℂ) :
    (∑ b : Fin 2, (complexFeatureCoord z b)^2) = ‖z‖^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [Fin.sum_univ_succ]
  simp [complexFeatureCoord]
  <;> ring

theorem complexPair_inner_real {ι : Type*} [Fintype ι]
    (c e : ι → ℂ) :
    ⟪(WithLp.toLp 2 (fun p : ι × Fin 2 => complexSourceCoord (c p.1) p.2)),
      (WithLp.toLp 2 (fun p : ι × Fin 2 => complexFeatureCoord (e p.1) p.2))⟫ =
      ∑ i, (c i * e i).re := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  change (∑ p : ι × Fin 2,
      complexSourceCoord (c p.1) p.2 * complexFeatureCoord (e p.1) p.2) = _
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ b : Fin 2, complexSourceCoord (c i) b * complexFeatureCoord (e i) b =
        ∑ i, (c i * e i).re := by
          apply Finset.sum_congr rfl
          intro i hi
          exact complex_pair_dot (c i) (e i)

/-- Real coordinate vector encoding a complex-valued feature family. The
second coordinate stores the negative imaginary part so its real dot product
with source coordinates gives the real part of the complex product. -/
def complexFeatureVector {ι : Type*} [Fintype ι] (e : ι → ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) :=
  WithLp.toLp 2 (fun p : ι × Fin 2 => complexFeatureCoord (e p.1) p.2)

def complexSourceVector {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) :=
  WithLp.toLp 2 (fun p : ι × Fin 2 => complexSourceCoord (c p.1) p.2)

theorem complexFeatureVector_norm_sq {ι : Type*} [Fintype ι] (e : ι → ℂ) :
    ‖complexFeatureVector e‖^2 = ∑ i, ‖e i‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [complexFeatureVector, WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ b : Fin 2, (complexFeatureCoord (e i) b)^2 = ∑ i, ‖e i‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact complex_feature_pair_norm_sq (e i)

theorem complex_source_pair_norm_sq (z : ℂ) :
    (∑ b : Fin 2, (complexSourceCoord z b)^2) = ‖z‖^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [Fin.sum_univ_succ]
  simp [complexSourceCoord]
  <;> ring

theorem complexSourceVector_norm_sq {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    ‖complexSourceVector c‖^2 = ∑ i, ‖c i‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [complexSourceVector, WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ b : Fin 2, (complexSourceCoord (c i) b)^2 = ∑ i, ‖c i‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact complex_source_pair_norm_sq (c i)

theorem complexPair_inner_real_vectors {ι : Type*} [Fintype ι]
    (c e : ι → ℂ) :
    ⟪complexSourceVector c, complexFeatureVector e⟫ =
      ∑ i, (c i * e i).re := by
  exact complexPair_inner_real c e

/-- Realified finite Fourier evaluation feature for a frequency set. -/
def torusFeature {d : ℕ} (S : Finset (Fin d → ℤ))
    (x : UnitAddTorus (Fin d)) : EuclideanSpace ℝ (S.attach × Fin 2) :=
  complexFeatureVector (fun k : S.attach => UnitAddTorus.mFourier k.1 x)

theorem torusFeature_norm_sq_le_card {d : ℕ} (S : Finset (Fin d → ℤ))
    (x : UnitAddTorus (Fin d)) : ‖torusFeature S x‖^2 ≤ S.card := by
  rw [torusFeature, complexFeatureVector_norm_sq]
  calc
    ∑ k : S.attach, ‖UnitAddTorus.mFourier k.1 x‖^2 ≤ ∑ _k : S.attach, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hnorm : ‖UnitAddTorus.mFourier k.1 x‖ = 1 := by
        simp [UnitAddTorus.mFourier, fourier_apply]
      nlinarith [sq_nonneg (‖UnitAddTorus.mFourier k.1 x‖)]
    _ = S.card := by simp

theorem torusFeature_norm_le_sqrt_card {d : ℕ} (S : Finset (Fin d → ℤ))
    (x : UnitAddTorus (Fin d)) : ‖torusFeature S x‖ ≤ Real.sqrt S.card := by
  have hnonneg : 0 ≤ ‖torusFeature S x‖ := norm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hnonneg hsqrt).1
  rw [Real.sq_sqrt (by positivity : 0 ≤ (S.card:ℝ))]
  exact torusFeature_norm_sq_le_card S x

theorem weighted_torusFeature_radius {d : ℕ} (S : Finset (Fin d → ℤ))
    (x : UnitAddTorus (Fin d)) (r : ℝ) (n : ℕ)
    (hcard : S.card ≤ 5^d * 2^n) :
    ‖(2:ℝ)^(-r*(n:ℝ)) • torusFeature S x‖ ≤
      Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^n := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-r*(n:ℝ)))]
  calc
    (2:ℝ)^(-r*(n:ℝ))*‖torusFeature S x‖ ≤
        (2:ℝ)^(-r*(n:ℝ))*Real.sqrt (S.card:ℝ) :=
      mul_le_mul_of_nonneg_left (torusFeature_norm_le_sqrt_card S x)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2:ℝ)^(-r*(n:ℝ))*Real.sqrt ((5:ℝ)^d*(2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hcard))
        (Real.rpow_nonneg (by norm_num) _)
    _ = Real.sqrt ((5:ℝ)^d)*((2:ℝ)^(1/2-r))^n := by
      rw [mul_comm, AlignmentPeriodicReconstruction.sqrt_dyadic_weight_identity]

/-- A mask's Hilbert radius is controlled by the number of its coordinates
and a uniform pointwise coordinate bound. This is the finite layer estimate
needed when realified Fourier coordinates are grouped by dyadic shape. -/
theorem coordinate_layer_radius_of_card
    {I G J : Type} [Fintype I] [DecidableEq J]
    (σ : I → J) (v : G → EuclideanSpace ℝ I) (j : J) {N : ℕ} {b : ℝ}
    (hb : 0 ≤ b)
    (hcard : (Finset.univ.filter (fun i : I => σ i = j)).card ≤ N)
    (hcoord : ∀ i g, σ i = j → |v g i| ≤ b) :
    ∀ g, ‖coordinateLayerMask σ j (v g)‖ ≤ Real.sqrt (N:ℝ)*b := by
  intro g
  let T : Finset I := Finset.univ.filter (fun i => σ i=j)
  have hnormsq : ‖coordinateLayerMask σ j (v g)‖^2 =
      ∑ i ∈ T, (v g i)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [coordinateLayerMask_apply, T, Finset.sum_filter]
  have hsum : ∑ i ∈ T, (v g i)^2 ≤ (T.card:ℝ)*b^2 := by
    calc
      ∑ i ∈ T, (v g i)^2 ≤ ∑ _i ∈ T, b^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hcoord i g (Finset.mem_filter.mp hi).2
        have hsquare := (sq_le_sq₀ (abs_nonneg (v g i)) hb).2 h
        simpa [sq_abs] using hsquare
      _ = (T.card:ℝ)*b^2 := by simp
  have hsum' : ∑ i ∈ T, (v g i)^2 ≤ (N:ℝ)*b^2 := by
    exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg b))
  have hsq : ‖coordinateLayerMask σ j (v g)‖^2 ≤ (Real.sqrt (N:ℝ)*b)^2 := by
    rw [hnormsq]
    simpa [Real.sq_sqrt (by positivity : 0 ≤ (N:ℝ)), mul_pow] using hsum'
  have hleft : 0 ≤ ‖coordinateLayerMask σ j (v g)‖ := norm_nonneg _
  have hright : 0 ≤ Real.sqrt (N:ℝ)*b := mul_nonneg (Real.sqrt_nonneg _) hb
  exact (sq_le_sq₀ hleft hright).1 hsq

abbrev FourierCoeffIndex {d : ℕ} (S : Finset (Fin d → ℕ)) :=
  Σ s : S, frequencyBox s.1

def periodicWeightedCoefficient {d : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (f : RealPeriodic d) (i : FourierCoeffIndex S) : ℂ :=
  ((Real.rpow (2:ℝ) (r*∑ j, (i.1.1 j:ℝ)):ℝ):ℂ) *
    ((tensorMultiplier i.1.1 i.2.1:ℂ)*realPeriodicFourierCoeff f i.2.1)

noncomputable def periodicSourceVector {d : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (f : RealPeriodic d) : EuclideanSpace ℝ (FourierCoeffIndex S × Fin 2) := by
  classical
  exact complexSourceVector (periodicWeightedCoefficient S r f)

noncomputable def periodicFeatureVector {d : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (x : UnitAddTorus (Fin d)) : EuclideanSpace ℝ (FourierCoeffIndex S × Fin 2) := by
  classical
  exact complexFeatureVector (fun i : FourierCoeffIndex S =>
    ((Real.rpow (2:ℝ) (-r*∑ j, (i.1.1 j:ℝ)):ℝ):ℂ)*UnitAddTorus.mFourier i.2.1 x)

def coefficientGrade {d : ℕ} {S : Finset (Fin d → ℕ)}
    (i : FourierCoeffIndex S) : ℕ := ∑ j, i.1.1 j

theorem complex_feature_coord_abs_le_norm (z : ℂ) (b : Fin 2) :
    |complexFeatureCoord z b| ≤ ‖z‖ := by
  fin_cases b <;> simp [complexFeatureCoord, Complex.abs_re_le_norm,
    Complex.abs_im_le_norm]

theorem periodicFeature_layer_radius {d : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (x : UnitAddTorus (Fin d)) {J : Type} [Fintype J] [DecidableEq J]
    (σ : FourierCoeffIndex S × Fin 2 → J) (j : J) (n : ℕ) {N : ℕ}
    (hgrade : ∀ i, σ i = j → coefficientGrade i.1 = n)
    (hcard : (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i=j)).card ≤ N) :
    ‖coordinateLayerMask σ j (periodicFeatureVector S r x)‖ ≤
      Real.sqrt (N:ℝ)*(2:ℝ)^(-r*(n:ℝ)) := by
  classical
  apply (coordinate_layer_radius_of_card σ (fun x => periodicFeatureVector S r x) j
    (by positivity) hcard ?_ ) x
  intro i x' hi
  have hg := hgrade i hi
  dsimp [periodicFeatureVector, complexFeatureVector]
  change |complexFeatureCoord
    (((Real.rpow (2:ℝ) (-r*∑ j_1, (i.1.1.1 j_1:ℝ)):ℝ):ℂ)*UnitAddTorus.mFourier i.1.2.1 x') i.2| ≤ _
  have hexp : -r * (∑ j, (i.1.1.1 j:ℝ)) = -r * (n:ℝ) := by
    congr 1
    exact_mod_cast hg
  rw [hexp]
  calc
    |complexFeatureCoord (((Real.rpow (2:ℝ) (-r*(n:ℝ))):ℂ)*UnitAddTorus.mFourier i.1.2.1 x') i.2| ≤
      ‖((Real.rpow (2:ℝ) (-r*(n:ℝ))):ℂ)*UnitAddTorus.mFourier i.1.2.1 x'‖ :=
        complex_feature_coord_abs_le_norm _ _
    _ = Real.rpow (2:ℝ) (-r*(n:ℝ))*‖UnitAddTorus.mFourier i.1.2.1 x'‖ := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < Real.rpow (2:ℝ) (-r*(n:ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [abs_of_pos hpos]
    _ ≤ Real.rpow (2:ℝ) (-r*(n:ℝ)) := by
      have hnorm : ‖UnitAddTorus.mFourier i.1.2.1 x'‖ = 1 := by
        simp [UnitAddTorus.mFourier, fourier_apply]
      rw [hnorm]
      simp

theorem periodicSourceVector_norm_sq {d : ℕ} (S : Finset (Fin d → ℕ))
    (r : ℝ) (f : RealPeriodic d) :
    ‖periodicSourceVector S r f‖^2 =
      ∑ s ∈ S, realBlockEnergy r f s := by
  classical
  rw [periodicSourceVector, complexSourceVector_norm_sq]
  change (∑ i : FourierCoeffIndex S, ‖periodicWeightedCoefficient S r f i‖^2) = _
  unfold FourierCoeffIndex
  rw [Fintype.sum_sigma]
  change (∑ s : S, ∑ k : frequencyBox s.1,
      ‖periodicWeightedCoefficient S r f ⟨s,k⟩‖^2) = _
  calc
    ∑ s : S, ∑ k : frequencyBox s.1,
        ‖periodicWeightedCoefficient S r f ⟨s,k⟩‖^2 =
      ∑ s ∈ S, realBlockEnergy r f s := by
      rw [← Finset.sum_coe_sort (s := S) (f := fun t => realBlockEnergy r f t)]
      apply Finset.sum_congr rfl
      intro s hs
      let w : ℝ := (2:ℝ)^(r*(∑ j : Fin d, (((s:Fin d→ℕ) j:ℝ))))
      let a : (Fin d → ℤ) → ℂ := fun k =>
        (tensorMultiplier (s:Fin d→ℕ) k:ℂ)*realPeriodicFourierCoeff f k
      have hcoeff : ∑ k : frequencyBox (s:Fin d→ℕ),
          ‖periodicWeightedCoefficient S r f ⟨s,k⟩‖^2 =
            w^2 * ∑ k ∈ frequencyBox (s:Fin d→ℕ), ‖a k‖^2 := by
        calc
          _ = ∑ k : frequencyBox (s:Fin d→ℕ), (w*‖a (k:Fin d→ℤ)‖)^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hwpos : 0 ≤ w := by simp [w, Real.rpow_nonneg]
            have hnorm : ‖periodicWeightedCoefficient S r f ⟨s,k⟩‖ =
                w * ‖a (k:Fin d→ℤ)‖ := by
              simp [periodicWeightedCoefficient, a, w, Complex.norm_mul,
                Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)]
            rw [hnorm]
          _ = w^2 * ∑ k : frequencyBox (s:Fin d→ℕ), ‖a (k:Fin d→ℤ)‖^2 := by
            simp_rw [mul_pow]
            rw [← Finset.mul_sum]
          _ = w^2 * ∑ k ∈ frequencyBox (s:Fin d→ℕ), ‖a k‖^2 := by
            rw [← Finset.sum_coe_sort (s := frequencyBox (s:Fin d→ℕ))
              (f := fun k => ‖a k‖^2)]
      rw [hcoeff]
      have hparseval := AlignmentTrigonometricL2.fourierPolynomial_L2_norm_sq
        (frequencyBox (s:Fin d→ℕ)) a
      have hblock : torusFourierPolynomial (frequencyBox (s:Fin d→ℕ)) a =
          block (s:Fin d→ℕ) f := by rfl
      rw [hblock] at hparseval
      have hparseval' : ‖(block (s:Fin d→ℕ) f).toLp 2
          (volume : Measure (UnitAddTorus (Fin d))) ℂ‖^2 =
          ∑ k ∈ frequencyBox (s:Fin d→ℕ), ‖a k‖^2 := by
        let μH : Measure (UnitAddTorus (Fin d)) :=
          Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
        have hmu : (volume : Measure (UnitAddTorus (Fin d))) = μH := by
          exact unitAddTorus_volume_eq_productHaar d
        have hnorm : eLpNorm (block (s:Fin d→ℕ) f) 2
            (volume : Measure (UnitAddTorus (Fin d))) =
            eLpNorm (block (s:Fin d→ℕ) f) 2 μH := by
          apply le_antisymm
          · apply eLpNorm_mono_measure
            rw [hmu]
          · apply eLpNorm_mono_measure
            rw [hmu]
        have h := hparseval
        change ‖(block (s:Fin d→ℕ) f).toLp 2 μH ℂ‖^2 = _ at h
        rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _)] at h
        rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ _)]
        rw [hnorm]
        exact h
      unfold realBlockEnergy
      rw [← hparseval']
      rw [← mul_pow]


theorem periodicSourceVector_feature_pairing {d : ℕ}
    (S : Finset (Fin d → ℕ)) (r : ℝ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    ⟪periodicSourceVector S r f, periodicFeatureVector S r x⟫ =
      ∑ s ∈ S, (block s f x).re := by
  classical
  rw [periodicSourceVector, periodicFeatureVector, complexPair_inner_real_vectors]
  unfold FourierCoeffIndex
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort (s := S) (f := fun t => (block t f x).re)]
  apply Finset.sum_congr rfl
  intro s hs
  change (∑ k : frequencyBox s.1,
      (periodicWeightedCoefficient S r f ⟨s, k⟩ *
        (((Real.rpow (2:ℝ) (-r * ∑ j, (s.1 j:ℝ)):ℝ):ℂ) *
          UnitAddTorus.mFourier k.1 x)).re) = (block s.1 f x).re
  have hblock : (block s.1 f x).re =
      ∑ k ∈ frequencyBox s.1,
        (((tensorMultiplier s.1 k:ℂ) * realPeriodicFourierCoeff f k) *
          UnitAddTorus.mFourier k x).re := by
    simp [block, torusFourierPolynomial, Finset.sum_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort (s := frequencyBox s.1)
    (f := fun k => (((tensorMultiplier s.1 k:ℂ) * realPeriodicFourierCoeff f k) *
      UnitAddTorus.mFourier k x).re)] at hblock
  rw [hblock]
  apply Fintype.sum_congr
  intro k
  change Complex.re (periodicWeightedCoefficient S r f ⟨s,k⟩ *
      (((Real.rpow (2:ℝ) (-r * ∑ j, (s.1 j:ℝ)):ℝ):ℂ) *
        UnitAddTorus.mFourier k.1 x)) =
    Complex.re (((tensorMultiplier s.1 k.1:ℂ) * realPeriodicFourierCoeff f k.1) *
      UnitAddTorus.mFourier k.1 x)
  apply congrArg Complex.re
  unfold periodicWeightedCoefficient
  let a : ℝ := r * ∑ j, (s.1 j:ℝ)
  have hpow : Real.rpow (2:ℝ) a * Real.rpow (2:ℝ) (-a) = 1 := by
    have hneg : Real.rpow (2:ℝ) (-a) = (Real.rpow (2:ℝ) a)⁻¹ :=
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) a
    rw [hneg]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) a))
  rw [show r * ∑ j, (s.1 j:ℝ) = a by rfl,
    show -r * ∑ j, (s.1 j:ℝ) = -a by dsimp [a]; ring]
  calc
    _ = (((Real.rpow (2:ℝ) a * Real.rpow (2:ℝ) (-a)):ℝ):ℂ) *
        (((tensorMultiplier s.1 k.1:ℂ) * realPeriodicFourierCoeff f k.1) *
          UnitAddTorus.mFourier k.1 x) := by push_cast; ring
    _ = _ := by rw [hpow]; simp

end BrownianSharp.AlignmentPeriodicWidthRealification
