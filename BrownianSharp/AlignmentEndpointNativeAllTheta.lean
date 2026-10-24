import BrownianSharp.AlignmentEndpointKernelInfinity
import BrownianSharp.FixedShapeDerivativeLp
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.NativeNikolskySynthesis

/-! Actual mixed-kernel profiles for the periodic L-infinity endpoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open BrownianSharp.ScalarKernelL1
open UnitAddTorus

/-- The mixed tensor kernel has the actual low/high coordinate L1 budget:
low coordinates use the uniform scalar-block bound, while high coordinates
use the proved inverse-profile decay. -/
theorem fixedShape_mixedKernel_integral_le_endpoint_profile
    {d : ℕ} (s t : Fin d → ℕ) (K : ℕ) (hK : Even K) (hKpos : 0 < K)
    (Lscalar Lprofile : ℝ) (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ q : ℕ, 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile) :
    let k : Fin d → ℕ := fun i => if s i < t i then K else 0
    (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, if s i < t i then
        ‖inverseProfileScale (t i) K‖ * Lprofile else Lscalar := by
  classical
  dsimp
  let k : Fin d → ℕ := fun i => if s i < t i then K else 0
  let Linv : Fin d → ℝ := fun i => ‖inverseProfileScale (t i) K‖ * Lprofile
  have hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)) := by
    intro i
    simp only [k]
    split_ifs with hit
    · right
      refine ⟨?_, ?_, ?_⟩
      · omega
      · exact hKpos
      · exact hK
    · left
      rfl
  have hbound := fixedShapeMixedKernel_integral_le t k Lscalar hLs
    hscalar Linv (fun i => mul_nonneg (norm_nonneg _) hLp) ?_
  · have hR : (∏ i : Fin d, if k i = 0 then Lscalar else Linv i) =
        ∏ i : Fin d, if s i < t i then Linv i else Lscalar := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hit : s i < t i <;> simp [k, Linv, hit]; have hk0 : K ≠ 0 := Nat.ne_of_gt hKpos; simp [hk0]
    change (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, if s i < t i then Linv i else Lscalar
    rw [← hR]
    exact hbound
  · intro i hk
    have hit : s i < t i := by
      by_contra hnot
      simp [k, hnot] at hk
    have ht : 0 < t i := Nat.zero_lt_of_lt hit
    exact ⟨ht, by simpa [k, hit] using hK, by
      simpa [Linv, k, hit] using hprofile (t i) ht⟩


/-- The literal p=∞ weighted block norm inherits coordinatewise dyadic
high-frequency decay from the actual inverse multiplier, with no finite-p
integral conversion. -/
theorem fixedShape_weightedBlockNorm_top_le_endpointProductDecay
    {d : ℕ} (s t : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (M r Lscalar Lprofile Czero CK : ℝ) (K : ℕ)
    (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (hr : 0 ≤ r) (hK : Even K) (hKpos : 0 < K)
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
    let k : Fin d → ℕ := fun i => if s i < t i then K else 0
    let C : Fin d → ℝ := fun i => if s i < t i then CK else Czero
    let H : Fin d → ℝ := fun i =>
      if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
      (fixedShapeSynthesis s c) ≤
      ENNReal.ofReal ((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)) *
        (M * ∏ i : Fin d, (H i * (C i * (2:ℝ)^(s i*k i))))) := by
  classical
  dsimp
  let k : Fin d → ℕ := fun i => if s i < t i then K else 0
  let C : Fin d → ℝ := fun i => if s i < t i then CK else Czero
  let H : Fin d → ℝ := fun i =>
    if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar
  have hCnonneg : ∀ i, 0 ≤ C i := by
    intro i
    simp [C]
    split_ifs <;> assumption
  have hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i := by
    intro i y
    simp only [k, C]
    split_ifs with hit
    · exact hderivK y
    · exact hderiv0 y
  have hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)) := by
    intro i
    simp only [k]
    split_ifs with hit
    · right
      exact ⟨by omega, by simpa [hKpos], hK⟩
    · exact Or.inl rfl
  have hHnonneg : ∀ i, 0 ≤ H i := by
    intro i
    simp [H]
    split_ifs <;> positivity
  have hkernel0 := fixedShapeMixedKernel_integral_le t k Lscalar hLs hscalar
      H hHnonneg (by
    intro i hk
    have hit : s i < t i := by
      by_contra hnot
      simp [k, hnot] at hk
    have ht : 0 < t i := Nat.zero_lt_of_lt hit
    have hInv := inverseProfileScale_norm_le_dyadic (t i) K
    have hprof := hprofile (t i) ht
    have hscaled :
        ‖inverseProfileScale (t i) K‖ * Lprofile ≤
          Lprofile * (((2:ℝ)^(t i))⁻¹ ^ K) := by
      calc
        _ = Lprofile * ‖inverseProfileScale (t i) K‖ := by ring
        _ ≤ Lprofile * (((2:ℝ)^(t i))⁻¹ ^ K) :=
          mul_le_mul_of_nonneg_left hInv hLp
    have hgoal := le_trans hprof hscaled
    exact ⟨ht, by simpa [k, hit] using hK, by simpa [H, k, hit] using hgoal⟩)
  have hR : (∏ i : Fin d, if k i = 0 then Lscalar else H i) =
      ∏ i : Fin d, H i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hit : s i < t i
    · have hKzero : K ≠ 0 := by omega
      simp [k, H, hit, hKzero]
    · simp [k, H, hit]
  have hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, H i := by
    rw [← hR]
    exact hkernel0
  have hLprod : 0 ≤ ∏ i : Fin d, H i :=
    Finset.prod_nonneg fun i hi => hHnonneg i
  convert fixedShape_weightedBlockNorm_top_le_of_coeff_bound
    s t k c hscale M hM hcoeff C hCnonneg hderiv
    (∏ i : Fin d, H i) hLprod hkernel r using 1
  congr 1
  rw [Finset.prod_mul_distrib]
  ring


/-- All profile constants used above exist from the checked scalar kernel,
inverse multiplier kernel, and compact smooth-atom derivative bounds. -/
theorem exists_endpoint_profile_constants {K : ℕ} (hK : Even K) :
    ∃ Lscalar Lprofile Czero CK : ℝ,
      0 ≤ Lscalar ∧ 0 ≤ Lprofile ∧ 0 ≤ Czero ∧ 0 ≤ CK ∧
      (∀ q : ℕ,
        (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
          ∂AddCircle.haarAddCircle) ≤ Lscalar) ∧
      (∀ q : ℕ, 0 < q →
        (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
          ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile) ∧
      (∀ y : ℝ, |iteratedDeriv 0 smoothAtom y| ≤ Czero) ∧
      (∀ y : ℝ, |iteratedDeriv K smoothAtom y| ≤ CK) := by
  obtain ⟨Lscalar, hLs, hscalar⟩ :=
    exists_scalarBlockKernel_uniform_L1_bound
  obtain ⟨Lprofile, hLp, hprofile⟩ :=
    exists_inverseMultiplierKernel_uniform_L1_bound hK
  obtain ⟨Czero, hC0, hderiv0⟩ := exists_smoothAtom_iteratedDeriv_bound 0
  obtain ⟨CK, hCK, hderivK⟩ := exists_smoothAtom_iteratedDeriv_bound K
  exact ⟨Lscalar, Lprofile, Czero, CK, hLs, hLp,
    le_of_lt hC0, le_of_lt hCK, hscalar, hprofile, hderiv0, hderivK⟩


private theorem dyadic_inverse_nat_pow_endpoint (a K : ℕ) :
    (((2:ℝ)^a)⁻¹)^K = (2:ℝ)^(-(a:ℝ)*(K:ℝ)) := by
  have hbase : (2:ℝ)^a = (2:ℝ)^(a:ℝ) := by simp
  rw [hbase, ← Real.rpow_natCast]
  rw [Real.inv_rpow (by positivity : 0 ≤ (2:ℝ)^(a:ℝ))]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

private theorem dyadic_inverse_gap_mul_endpoint (s t K : ℕ) (hst : s < t) :
    (((2:ℝ)^t)⁻¹)^K * (2:ℝ)^(s*K) =
      (2:ℝ)^(-((K:ℝ) * ((t-s:ℕ):ℝ))) := by
  rw [dyadic_inverse_nat_pow_endpoint t K, ← Real.rpow_natCast (2:ℝ) (s*K)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  have hsub : s + (t-s) = t := Nat.add_sub_of_le (Nat.le_of_lt hst)
  have hsubR : (s:ℝ) + ((t-s:ℕ):ℝ) = (t:ℝ) := by exact_mod_cast hsub
  rw [← hsubR]
  simp only [Nat.cast_mul]
  ring

private theorem endpoint_high_weight_eq (s t K : ℕ) (r : ℝ) (hst : s < t) :
    (2:ℝ)^(r*(t:ℝ)) * (2:ℝ)^(-((K:ℝ)*((t-s:ℕ):ℝ))) =
      (2:ℝ)^(r*(s:ℝ)) * (2:ℝ)^(-((K:ℝ)-r)*((t-s:ℕ):ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2), ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  have hg : (s:ℝ) + ((t-s:ℕ):ℝ) = (t:ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le (Nat.le_of_lt hst))
  rw [← hg]
  ring

private theorem endpoint_low_weight_eq (s t : ℕ) (r : ℝ) (hts : t ≤ s) :
    (2:ℝ)^(r*(t:ℝ)) = (2:ℝ)^(r*(s:ℝ)) * (2:ℝ)^(-r*((s-t:ℕ):ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  have hg : (t:ℝ) + ((s-t:ℕ):ℝ) = (s:ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hts)
  rw [← hg]
  ring

private theorem prod_le_prod_nonneg_real_endpoint {ι : Type*} (s : Finset ι)
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

/-- Real coordinate profile used for the subsequent powered discrete Young
estimate. -/
def endpointNikolskyShapeWeightReal {d : ℕ} (s t : Fin d → ℕ)
    (r : ℝ) (K : ℕ) : ℝ :=
  ∏ i : Fin d, if t i ≤ s i then
    (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
  else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))

/-- Factor the actual scalar/inverse block profile into its source-scale size
and its low/high geometric displacement. -/
theorem endpoint_product_profile_factor
    {d n : ℕ} (s t : Fin d → ℕ) (M r Lscalar Lprofile Czero CK : ℝ)
    (K : ℕ) (hM : 0 ≤ M) (hr : 0 ≤ r) (hK : Even K)
    (hKpos : 0 < K) (hrK : r < K)
    (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hC0 : 0 ≤ Czero) (hCK : 0 ≤ CK)
    (hsum : ∑ i : Fin d, s i = n) :
    (2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)) *
      (M * ∏ i : Fin d,
        ((if s i < t i then
            Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
          ((if s i < t i then CK else Czero) *
            (2:ℝ)^(s i*(if s i < t i then K else 0)))) ) ≤
      M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ)) * endpointNikolskyShapeWeightReal s t r K := by
  classical
  let D : ℝ := max (Lscalar*Czero) (Lprofile*CK)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoord : ∀ i : Fin d,
      (2:ℝ)^(r*(t i:ℝ)) *
        ((if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
          ((if s i < t i then CK else Czero) *
            (2:ℝ)^(s i*(if s i < t i then K else 0)))) ≤
      D * (2:ℝ)^(r*(s i:ℝ)) *
        (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
          else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))) := by
    intro i
    by_cases hit : s i < t i
    · have hgap := dyadic_inverse_gap_mul_endpoint (s i) (t i) K hit
      have hbase :
          (Lprofile*((2:ℝ)^(t i))⁻¹ ^ K) * (CK*(2:ℝ)^(s i*K)) ≤
            (Lprofile*CK)*(2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ))) := by
        calc
          _ = (Lprofile*CK)*(((2:ℝ)^(t i))⁻¹ ^ K * (2:ℝ)^(s i*K)) := by ring
          _ = _ := by rw [hgap]
          _ ≤ _ := le_rfl
      have hconst : Lprofile*CK ≤ D := le_max_right _ _
      simp only [if_pos hit, if_neg (Nat.not_le_of_gt hit)]
      calc
        _ ≤ (2:ℝ)^(r*(t i:ℝ)) *
            ((Lprofile*CK) * (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ)))) :=
              mul_le_mul_of_nonneg_left hbase (by positivity)
        _ = (Lprofile*CK) *
            ((2:ℝ)^(r*(t i:ℝ)) *
              (2:ℝ)^(-((K:ℝ)*((t i-s i:ℕ):ℝ)))) := by ring
        _ = (Lprofile*CK) *
            ((2:ℝ)^(r*(s i:ℝ)) *
              (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))) := by
                rw [endpoint_high_weight_eq (s i) (t i) K r hit]
        _ ≤ D * (2:ℝ)^(r*(s i:ℝ)) *
            (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ)) := by
              calc
                _ ≤ D * ((2:ℝ)^(r*(s i:ℝ)) *
                    (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))) :=
                  mul_le_mul_of_nonneg_right hconst (by positivity)
                _ = _ := by ring
    · have hts : t i ≤ s i := Nat.le_of_not_gt hit
      have hconst : Lscalar*Czero ≤ D := le_max_left _ _
      simp only [if_neg hit, if_pos hts]
      have heq := endpoint_low_weight_eq (s i) (t i) r hts
      calc
        _ = (Lscalar*Czero) * (2:ℝ)^(r*(t i:ℝ)) := by ring
        _ = (Lscalar*Czero) *
            ((2:ℝ)^(r*(s i:ℝ)) *
              (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))) := by rw [heq]
        _ ≤ D * ((2:ℝ)^(r*(s i:ℝ)) *
            (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))) :=
              mul_le_mul_of_nonneg_right hconst (mul_nonneg (by positivity) (by positivity))
        _ = D * (2:ℝ)^(r*(s i:ℝ)) *
            (2:ℝ)^(-r*((s i-t i:ℕ):ℝ)) := by ring
  have hleftnon : ∀ i : Fin d, 0 ≤
      (2:ℝ)^(r*(t i:ℝ)) *
        ((if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
          ((if s i < t i then CK else Czero) *
            (2:ℝ)^(s i*(if s i < t i then K else 0)))) := by
    intro i
    positivity
  have hrightnon : ∀ i : Fin d, 0 ≤ D * (2:ℝ)^(r*(s i:ℝ)) *
        (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
          else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))) := by
    intro i
    positivity
  have hprod := prod_le_prod_nonneg_real_endpoint Finset.univ
    (fun i => (2:ℝ)^(r*(t i:ℝ)) *
      ((if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
        ((if s i < t i then CK else Czero) *
          (2:ℝ)^(s i*(if s i < t i then K else 0)))))
    (fun i => D * (2:ℝ)^(r*(s i:ℝ)) *
      (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
        else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ))))
    (by intro i hi; exact hleftnon i)
    (by intro i hi; exact hrightnon i) (by intro i hi; exact hcoord i)
  have hsumT : (2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)) =
      ∏ i : Fin d, (2:ℝ)^(r*(t i:ℝ)) := by
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  have hsumS : ∏ i : Fin d, (2:ℝ)^(r*(s i:ℝ)) =
      (2:ℝ)^(r*(n:ℝ)) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum]
  let P : Fin d → ℝ := fun i => (2:ℝ)^(r*(t i:ℝ))
  let Q : Fin d → ℝ := fun i =>
    (if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar) *
      ((if s i < t i then CK else Czero) *
        (2:ℝ)^(s i*(if s i < t i then K else 0)))
  have hsplit : (∏ i : Fin d, P i) * (∏ i : Fin d, Q i) =
      ∏ i : Fin d, (P i * Q i) := (Finset.prod_mul_distrib).symm
  rw [hsumT]
  calc
    _ = M * ((∏ i : Fin d, P i) * (∏ i : Fin d, Q i)) := by ring
    _ = M * ∏ i : Fin d, (P i * Q i) := by rw [hsplit]
    _ ≤ M * ∏ i : Fin d,
        (D * (2:ℝ)^(r*(s i:ℝ)) *
          (if t i ≤ s i then (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
            else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ)))) :=
          mul_le_mul_of_nonneg_left hprod hM
    _ = M * D^d * (2:ℝ)^(r*(n:ℝ)) *
        endpointNikolskyShapeWeightReal s t r K := by
          calc
            _ = M * ((∏ i : Fin d, D) *
                (∏ i : Fin d, (2:ℝ)^(r*(s i:ℝ))) *
                (∏ i : Fin d, if t i ≤ s i then
                  (2:ℝ)^(-r*((s i-t i:ℕ):ℝ))
                else (2:ℝ)^(-((K:ℝ)-r)*((t i-s i:ℕ):ℝ)))) := by
                  congr 1
                  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            _ = _ := by
                  simp [endpointNikolskyShapeWeightReal, hsumS, mul_assoc]

