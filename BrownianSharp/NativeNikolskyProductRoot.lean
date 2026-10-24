import BrownianSharp.NativeNikolskyEndpoint
import Mathlib.Tactic

/-! Fixed-shape conversion from the exact native block integral bound to the
coordinatewise Nikolsky weight. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockVariance


/-- The dyadic profile factors from the integral estimate have exactly the
Nikolsky coordinate exponents after multiplication by the block weight. -/
theorem dyadicShapeWeightedFactor_eq_public {d : ℕ}
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
      _ = _ := by rw [Finset.prod_mul_distrib]; rfl
  have ht : (2:ℝ)^(r * ∑ i, (t i:ℝ)) =
      ∏ i : Fin d, (2:ℝ)^(r*(t i:ℝ)) := by
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
  have hs' : ∏ i : Fin d, (2:ℝ)^(r*(s i:ℝ)) = (2:ℝ)^(r*(n:ℝ)) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum]
  rw [ht, ← hs']
  exact hprod


private theorem finset_prod_rpow_of_nonneg_local {ι : Type*} (s : Finset ι)
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

private theorem product_inv_dyadic_eq {d : ℕ} (s : Fin d → ℕ) (n : ℕ)
    (hsum : ∑ i, s i = n) :
    (∏ i : Fin d, ((2:ℝ)^(s i))⁻¹) = ((2:ℝ)^n)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  have hprod : (∏ i : Fin d, (2:ℝ)^(s i)) = (2:ℝ)^n := by
    simp_rw [← Real.rpow_natCast (2:ℝ)]
    rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    rw [← Nat.cast_sum, hsum]
  exact hprod

private theorem dyadic_inverse_nat_pow_public (a K : ℕ) :
    (((2:ℝ)^a)⁻¹)^K = (2:ℝ)^(-(a:ℝ)*(K:ℝ)) := by
  have hbase : (2:ℝ)^a = (2:ℝ)^(a:ℝ) := by simp
  rw [hbase, ← Real.rpow_natCast]
  rw [Real.inv_rpow (by positivity : 0 ≤ (2:ℝ)^(a:ℝ))]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

private theorem dyadic_inverse_gap_mul_public (s t K : ℕ) (hst : s < t) :
    (((2:ℝ)^t)⁻¹)^K * (2:ℝ)^(s*K) =
      (2:ℝ)^(-((K:ℝ)*((t-s:ℕ):ℝ))) := by
  rw [dyadic_inverse_nat_pow_public t K, ← Real.rpow_natCast (2:ℝ) (s*K)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  have hsub : s + (t-s)=t := Nat.add_sub_of_le (Nat.le_of_lt hst)
  have hsubR : (s:ℝ)+((t-s:ℕ):ℝ)=(t:ℝ) := by exact_mod_cast hsub
  rw [← hsubR]
  simp only [Nat.cast_mul]
  ring

private theorem prod_le_prod_nonneg_real_local {ι : Type*} (s : Finset ι)
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

/-- The exact fixed-shape Nikolsky conversion. The coefficient p-energy bound
cancels the `2^{-sum s/p}` factor from the spatial integral. All remaining
constants depend on the fixed dimension, exponent, and kernel profiles, but
not on n, s, t, or the coefficient vector. -/
theorem fixedShape_weightedBlockNorm_le_nikolskyShape
    {d n : ℕ} (s : Fin d → ℕ) (t : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p r : ℝ) (hp : 1 ≤ p) (K : ℕ) (hK : Even K) (hKpos : 0 < K)
    (Lscalar Lprofile Cderiv G : ℝ)
    (hLscalar : 0 ≤ Lscalar) (hLprofile : 0 ≤ Lprofile)
    (hCderiv : 0 ≤ Cderiv) (hG : 0 ≤ G)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ (q : ℕ), 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv : ∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ Cderiv)
    (hsum : ∑ i, s i = n)
    (hcoeff : (∑ j : DyadicShapeCell d s, |c j| ^ p) ≤
      2 * (2:ℝ)^n * G) :
    SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
      (fixedShapeSynthesis s c) ≤
    ENNReal.ofReal (((2*G)^(1/p)) *
      (Lscalar+Lprofile)^d * (1+Cderiv)^d *
      (2:ℝ)^(r*(n:ℝ)) * nativeNikolskyShapeWeightReal s t r K) := by
  let L := Lscalar + Lprofile
  let M := 1 + Cderiv
  let P : Fin d → ℝ := fun i => if s i < t i then
    ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar
  let Q : Fin d → ℝ := fun i => (if s i < t i then Cderiv else 1) *
    (2:ℝ)^(s i * (if s i < t i then K else 0))
  let decay : Fin d → ℝ := fun i => if s i < t i then
    (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) else 1
  let U : ℝ := L^d * M^d * ∏ i : Fin d, decay i
  let B : ℝ := U^p * (2*G)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hP : ∀ i, 0 ≤ P i := by
    intro i
    dsimp [P]
    split_ifs <;> positivity
  have hQ : ∀ i, 0 ≤ Q i := by
    intro i
    dsimp [Q]
    split_ifs <;> positivity
  have hdecay : ∀ i, 0 ≤ decay i := by
    intro i
    dsimp [decay]
    split_ifs <;> positivity
  have hcoord : ∀ i : Fin d, P i * Q i ≤ L * M * decay i := by
    intro i
    by_cases hst : s i < t i
    · have hscale := inverseProfileScale_norm_le_dyadic (t i) K
      have hLprof : Lprofile ≤ L := by dsimp [L]; linarith
      have hder : Cderiv ≤ M := by dsimp [M]; linarith
      have hbase0 := mul_le_mul hscale hLprof (by positivity)
        (by positivity : 0 ≤ ((2:ℝ)^(t i))⁻¹ ^ K)
      have hbase : ‖inverseProfileScale (t i) K‖ * Lprofile ≤
          L * ((2:ℝ)^(t i))⁻¹ ^ K := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hbase0
      have hq := mul_le_mul_of_nonneg_right hder
        (by positivity : 0 ≤ (2:ℝ)^(s i*K))
      have hcombine : ‖inverseProfileScale (t i) K‖ * Lprofile *
          (Cderiv * (2:ℝ)^(s i*K)) ≤
          (L * ((2:ℝ)^(t i))⁻¹ ^ K) * (M*(2:ℝ)^(s i*K)) := by
        have hq' : Cderiv * (2:ℝ)^(s i*K) ≤ M*(2:ℝ)^(s i*K) := by
          simpa [mul_comm] using hq
        exact mul_le_mul hbase hq' (by positivity) (by positivity)
      have hgap := dyadic_inverse_gap_mul_public (s i) (t i) K hst
      dsimp [P,Q,decay]
      simp [hst, Nat.not_le_of_gt hst]
      calc
        _ ≤ (L * (((2:ℝ)^(t i))⁻¹ ^ K) * (M*(2:ℝ)^(s i*K))) := by
          exact hcombine
        _ = L*M*(((2:ℝ)^(t i))⁻¹ ^ K * (2:ℝ)^(s i*K)) := by ring
        _ = L*M*((2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ)))) := by rw [hgap]
    · have hts : t i ≤ s i := Nat.le_of_not_gt hst
      have hLscalar : Lscalar ≤ L := by dsimp [L]; linarith
      have hder : (1:ℝ) ≤ M := by dsimp [M]; linarith
      have hpow : (2:ℝ)^(s i*(if s i < t i then K else 0)) = 1 := by simp [hst]
      dsimp [P,Q,decay]
      simp [hst, hts]
      calc
        _ = Lscalar * 1 := by simp
        _ ≤ L * M := by nlinarith [hLscalar, hder]
  have hPQ : (∏ i : Fin d, P i) * (∏ i : Fin d, Q i) ≤ U := by
    have hp := prod_le_prod_nonneg_real_local Finset.univ
      (fun i => P i * Q i) (fun i => L * M * decay i)
      (fun i hi => mul_nonneg (hP i) (hQ i))
      (fun i hi => mul_nonneg (mul_nonneg hL hM) (hdecay i))
      (fun i hi => hcoord i)
    calc
      _ = ∏ i : Fin d, (P i * Q i) := by rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ i : Fin d, (L * M * decay i) := hp
      _ = U := by
        dsimp [U]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        simp [Finset.prod_const]
  have hQprod : (∏ i : Fin d, ((2:ℝ)^(s i))⁻¹ * (Q i)^p) =
      ((2:ℝ)^n)⁻¹ * (∏ i : Fin d, Q i)^p := by
    rw [Finset.prod_mul_distrib, product_inv_dyadic_eq s n hsum,
      finset_prod_rpow_of_nonneg_local Finset.univ Q p (by intro i hi; exact hQ i)]
  have hnative := fixedShapeBlock_nativeDecay_integral s t c p hp K hK hKpos
    Lscalar Lprofile Cderiv hLscalar hLprofile hCderiv hscalar hprofile hderiv
  have hnative' : (∫ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, P i)^p *
        (((2:ℝ)^n)⁻¹ * (∏ i : Fin d, Q i)^p) *
        (∑ j : DyadicShapeCell d s, |c j|^p) := by
    have hn := hnative
    change (∫ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, P i)^p *
        (∏ i : Fin d, ((2:ℝ)^(s i))⁻¹ * (Q i)^p) *
        (∑ j : DyadicShapeCell d s, |c j|^p) at hn
    rw [hQprod] at hn
    exact hn
  have hprodNonneg : 0 ≤ (∏ i : Fin d, P i) * (∏ i : Fin d, Q i) :=
    mul_nonneg (Finset.prod_nonneg fun i hi => hP i)
      (Finset.prod_nonneg fun i hi => hQ i)
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hpow : ((∏ i : Fin d, P i) * (∏ i : Fin d, Q i))^p ≤ U^p :=
    Real.rpow_le_rpow hprodNonneg hPQ (by linarith [hp])
  have hcoefScale : ((2:ℝ)^n)⁻¹ *
      (∑ j : DyadicShapeCell d s, |c j|^p) ≤ 2*G := by
    calc
      _ ≤ ((2:ℝ)^n)⁻¹ * (2*(2:ℝ)^n*G) := by
        apply mul_le_mul_of_nonneg_left hcoeff
        positivity
      _ = 2*G := by field_simp
  have hInt : (∫ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ B := by
    have hcombine : (∏ i : Fin d, P i)^p * (∏ i : Fin d, Q i)^p =
        ((∏ i : Fin d, P i) * (∏ i : Fin d, Q i))^p := by
      symm
      exact Real.mul_rpow (Finset.prod_nonneg fun i hi => hP i)
        (Finset.prod_nonneg fun i hi => hQ i)
    calc
      _ ≤ (∏ i : Fin d, P i)^p *
          (((2:ℝ)^n)⁻¹ * (∏ i : Fin d, Q i)^p) *
          (∑ j : DyadicShapeCell d s, |c j|^p) := hnative'
      _ = ((∏ i : Fin d, P i)^p * (∏ i : Fin d, Q i)^p) *
          (((2:ℝ)^n)⁻¹ * (∑ j : DyadicShapeCell d s, |c j|^p)) := by ring
      _ = ((∏ i : Fin d, P i) * (∏ i : Fin d, Q i))^p *
          (((2:ℝ)^n)⁻¹ * (∑ j : DyadicShapeCell d s, |c j|^p)) := by rw [hcombine]
      _ ≤ U^p * (2*G) := by
        exact mul_le_mul hpow hcoefScale (by positivity) (by positivity)
      _ = B := by rfl
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm := weightedBlockNorm_le_of_integral_bound
    (fixedShapeSynthesis s c) t p r B (by linarith [hp]) hB hInt
  have hroot : B^(1/p) = U*(2*G)^(1/p) := by
    dsimp [B]
    rw [Real.mul_rpow (Real.rpow_nonneg hU p) (by positivity : 0 ≤ 2*G)]
    rw [← Real.rpow_mul hU p (1/p)]
    have hp0 : p ≠ 0 := by linarith [hp]
    have hexp : p*(1/p)=1 := by field_simp
    rw [hexp, Real.rpow_one]
  have hscale :
      (2:ℝ)^(r*∑ i, (t i:ℝ)) * B^(1/p) =
      (2*G)^(1/p) * (Lscalar+Lprofile)^d * (1+Cderiv)^d *
        (2:ℝ)^(r*(n:ℝ)) * nativeNikolskyShapeWeightReal s t r K := by
    rw [hroot]
    dsimp [U, L, M]
    calc
      _ = ((2*G)^(1/p) * (Lscalar+Lprofile)^d * (1+Cderiv)^d) *
          ((2:ℝ)^(r*∑ i, (t i:ℝ)) *
            ∏ i : Fin d, decay i) := by
              simp [decay]
              ring
      _ = _ := by
        rw [dyadicShapeWeightedFactor_eq_public s t r K n hsum]
        ring
  have hnorm' : SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
      (fixedShapeSynthesis s c) ≤ ENNReal.ofReal
        ((2*G)^(1/p) * (Lscalar+Lprofile)^d * (1+Cderiv)^d *
          (2:ℝ)^(r*(n:ℝ)) * nativeNikolskyShapeWeightReal s t r K) := by
    rw [← hscale]
    exact hnorm
  exact hnorm'


end BrownianSharp
