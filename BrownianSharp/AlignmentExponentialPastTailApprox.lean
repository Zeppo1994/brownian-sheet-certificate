import BrownianSharp.AlignmentFractionalPastTailFiltration
import BrownianSharp.AlignmentFractionalPastTailPartition
import BrownianSharp.AlignmentFractionalPastTailL2Approx
import BrownianSharp.AlignmentFractionalPastTailTaylor
import BrownianSharp.AlignmentFractionalPastTailScaling
import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! Actual coefficient vectors for the refined, one-sided Taylor filtration of
the MvN past-tail kernel. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BrownianSharp.AlignmentExponentialPastTailApprox

open BrownianSharp.AlignmentFractionalPastTail
open BrownianSharp.AlignmentFractionalPastTailL2Approx
open BrownianSharp.AlignmentFractionalPastTailPartition
open BrownianSharp.AlignmentFractionalGeometricPartition
open BrownianSharp.AlignmentFractionalPastTailFiltration
open BrownianSharp.AlignmentFractionalHilbertTaylor
open BrownianSharp.AlignmentGeometricRanks

abbrev PastL2 := Lp ℝ 2 (volume.restrict (Set.Ioi (0:ℝ)))

theorem pieceRight_pos_le_one (J : ℕ) (i : Option (Fin J) × Fin 4) :
    0 < pieceRight J i ∧ pieceRight J i ≤ 1 := by
  rcases i with ⟨base,k⟩
  cases base with
  | none =>
      fin_cases k <;> norm_num [pieceRight, coarseRight]
  | some j =>
      have hcpos : 0 < shellScale j := by
        dsimp [shellScale]
        positivity
      have hcle : shellScale j ≤ 1 := by
        dsimp [shellScale]
        have hpow : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
        exact (div_le_one₀ (by positivity)).2 hpow
      fin_cases k <;> simp only [pieceRight, shellRight] <;>
        norm_num at * <;> constructor <;> nlinarith

theorem piece_geometry (J : ℕ) (i : Option (Fin J) × Fin 4) :
    0 < pieceLeft J i ∧ pieceLeft J i ≤ pieceRight J i ∧
      pieceRight J i ≤ 1 ∧ pieceRight J i - pieceLeft J i ≤ pieceLeft J i / 2 := by
  rcases i with ⟨base,k⟩
  cases base with
  | none =>
      fin_cases k <;> norm_num [pieceLeft, pieceRight, coarseLeft, coarseRight]
  | some j =>
      have hcpos : 0 < shellScale j := by
        dsimp [shellScale]
        positivity
      have hcle : shellScale j ≤ 1 := by
        dsimp [shellScale]
        have hpow : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
        exact (div_le_one₀ (by positivity)).2 hpow
      have hratio (k : Fin 4) :
          0 < (if k.val = 0 then (1/4:ℝ) else if k.val = 1 then 3/8
            else if k.val = 2 then 9/16 else 27/32) ∧
          (if k.val = 0 then (1/4:ℝ) else if k.val = 1 then 3/8
            else if k.val = 2 then 9/16 else 27/32) ≤
          (if k.val = 0 then (3/8:ℝ) else if k.val = 1 then 9/16
            else if k.val = 2 then 27/32 else 1) ∧
          (if k.val = 0 then (3/8:ℝ) else if k.val = 1 then 9/16
            else if k.val = 2 then 27/32 else 1) ≤ 1 ∧
          ((if k.val = 0 then (3/8:ℝ) else if k.val = 1 then 9/16
            else if k.val = 2 then 27/32 else 1) -
          (if k.val = 0 then (1/4:ℝ) else if k.val = 1 then 3/8
            else if k.val = 2 then 9/16 else 27/32)) ≤
          (if k.val = 0 then (1/4:ℝ) else if k.val = 1 then 3/8
            else if k.val = 2 then 9/16 else 27/32)/2 := by
        fin_cases k <;> norm_num
      have := hratio k
      simp only [pieceLeft, pieceRight, shellLeft, shellRight]
      constructor
      · positivity
      · constructor
        · exact mul_le_mul_of_nonneg_left this.2.1 hcpos.le
        · constructor
          · calc
              shellScale j * (if k.val = 0 then (3/8:ℝ) else if k.val = 1 then 9/16
                else if k.val = 2 then 27/32 else 1) ≤
                  1 * (if k.val = 0 then (3/8:ℝ) else if k.val = 1 then 9/16
                    else if k.val = 2 then 27/32 else 1) :=
                mul_le_mul_of_nonneg_right hcle (by positivity)
              _ ≤ 1 := by nlinarith [this.2.2.1]
          · have hw := mul_le_mul_of_nonneg_left this.2.2.2 hcpos.le
            nlinarith

def permanentCenter : PastTailTaylorIndex → ℝ
  | .coarse k => coarseRight k
  | .shell j k => (1/(2:ℝ)^j) *
      (if k.val = 0 then 3/8 else if k.val = 1 then 9/16
        else if k.val = 2 then 27/32 else 1)

theorem permanentCenter_pos_le_one (i : PastTailTaylorIndex) :
    0 < permanentCenter i ∧ permanentCenter i ≤ 1 := by
  cases i with
  | coarse k =>
      fin_cases k <;> norm_num [permanentCenter, coarseRight]
  | shell j k =>
      have hcpos : 0 < (1/(2:ℝ)^j) := by positivity
      have hcle : (1/(2:ℝ)^j) ≤ 1 := by
        have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
        exact (div_le_one₀ (by positivity)).2 hp
      fin_cases k
      · simp only [permanentCenter]
        constructor
        · positivity
        · calc
            (1/(2:ℝ)^j) * (3/8) ≤ 1*(3/8) :=
              mul_le_mul_of_nonneg_right hcle (by norm_num)
            _ ≤ 1 := by norm_num
      · simp only [permanentCenter]
        constructor
        · positivity
        · calc
            (1/(2:ℝ)^j) * (9/16) ≤ 1*(9/16) :=
              mul_le_mul_of_nonneg_right hcle (by norm_num)
            _ ≤ 1 := by norm_num
      · simp only [permanentCenter]
        constructor
        · positivity
        · calc
            (1/(2:ℝ)^j) * (27/32) ≤ 1*(27/32) :=
              mul_le_mul_of_nonneg_right hcle (by norm_num)
            _ ≤ 1 := by norm_num
      · simp only [permanentCenter]
        constructor
        · positivity
        · norm_num [permanentCenter]
          simpa [one_div] using hcle

/-- One permanent source vector for each local Taylor coefficient. -/
def pastTailCoeffVector (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (i : PastTailTaylorIndex) (k : ℕ) : PastL2 :=
  (pastTailTaylorCoeff_memLp hp0 hp1
    (permanentCenter_pos_le_one i).1 (permanentCenter_pos_le_one i).2).toLp
      (pastTailTaylorCoeff p k (permanentCenter i))

def pastTailCoeffFamily (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (M : ℕ) :
    PastTailTaylorIndex → Fin M → PastL2 :=
  fun z k => pastTailCoeffVector p hp0 hp1 z k.val

def pastTailCenter (J : ℕ) (i : Option (Fin J) × Fin 4) : ℝ :=
  permanentCenter (embedIndex J i)

def pastTailParameterVector (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : PastL2 :=
  (pastTailPower_memLp_two hp0 hp1 ht0 ht1).toLp (pastTailPower p t)

theorem pastTailCoeffVector_coe_ae (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (i : PastTailTaylorIndex) (k : ℕ) :
      (↑(pastTailCoeffVector p hp0 hp1 i k) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun x => pastTailTaylorCoeff p k (permanentCenter i) x := by
  exact (pastTailTaylorCoeff_memLp hp0 hp1
    (permanentCenter_pos_le_one i).1 (permanentCenter_pos_le_one i).2).coeFn_toLp

theorem pastTailCenter_eq_pieceRight (J : ℕ) (i : Option (Fin J) × Fin 4) :
    pastTailCenter J i = pieceRight J i := by
  rcases i with ⟨base,k⟩
  cases base <;> fin_cases k <;>
    simp [pastTailCenter, permanentCenter, embedIndex, pieceRight,
      coarseRight, shellRight, shellScale]

theorem pastTailParameterVector_coe_ae (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (↑(pastTailParameterVector p hp0 hp1 t ht0 ht1) : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Ioi 0)] fun x => pastTailPower p t x := by
  exact (pastTailPower_memLp_two hp0 hp1 ht0 ht1).coeFn_toLp

theorem pastTail_localTaylor_coe_ae (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (J M : ℕ) (hM : 0 < M)
    (i : Option (Fin J) × Fin 4) (t : ℝ) :
    (↑(localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
        (pastTailCenter J) i t) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioi 0)]
      fun x => pastTailTaylorPoly p M (pieceRight J i) t x := by
  classical
  rw [← pastTailCenter_eq_pieceRight J i]
  let v : Fin M → PastL2 := fun k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val
  let b := pastTailCenter J i
  have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin M))
    (fun k => (t-b)^(k.val) • v k)
  have hcoeff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ k : Fin M, (↑(v k) : ℝ → ℝ) x = pastTailTaylorCoeff p k.val b x := by
    apply ae_all_iff.mpr
    intro k
    exact pastTailCoeffVector_coe_ae p hp0 hp1 (embedIndex J i) k.val
  have hsmul : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ∀ k : Fin M, (↑((t-b)^(k.val) • v k) : ℝ → ℝ) x =
        (t-b)^(k.val) * (↑(v k) : ℝ → ℝ) x := by
    apply ae_all_iff.mpr
    intro k
    exact Lp.coeFn_smul ((t-b)^(k.val)) (v k)
  filter_upwards [hsum, hcoeff, hsmul] with x hsum hxcoeff hxsmul
  change (↑(∑ k : Fin M, (t-b)^(k.val) • v k) : ℝ → ℝ) x = _
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  calc
    (∑ k : Fin M, (↑((t-b)^(k.val) • v k) : ℝ → ℝ) x) =
        ∑ k : Fin M, (t-b)^(k.val) * pastTailTaylorCoeff p k.val b x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hxsmul k, hxcoeff k]
    _ =
        ∑ k ∈ Finset.range M, (t-b)^k * pastTailTaylorCoeff p k b x :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        (t-b)^k * pastTailTaylorCoeff p k b x) M
    _ = pastTailTaylorPoly p M b t x :=
      (pastTailTaylorPoly_eq_coeff_sum (by exact_mod_cast hM)).symm

theorem pastTail_localTaylor_error_norm_le (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (J M : ℕ) (hM : 0 < M)
    (i : Option (Fin J) × Fin 4) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwi : refinedWeight J i t ≠ 0) :
    ‖pastTailParameterVector p hp0 hp1 t ht0 ht1 -
      localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
        (pastTailCenter J) i t‖ ≤ (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^M := by
  let a := pieceLeft J i
  let b := pieceRight J i
  have hgeom := piece_geometry J i
  have hsupp := refinedWeight_support ht0 ht1 i hwi
  have hbound := pastTailTaylor_error_eLpNorm_uniform hp0 hp1 hM
    hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2 hsupp.1 hsupp.2
  have hcoe : (↑(pastTailParameterVector p hp0 hp1 t ht0 ht1 -
      localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
        (pastTailCenter J) i t) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioi 0)]
        fun x => pastTailPower p t x - pastTailTaylorPoly p M b t x := by
    filter_upwards [Lp.coeFn_sub
        (pastTailParameterVector p hp0 hp1 t ht0 ht1)
        (localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
          (pastTailCenter J) i t),
      pastTailParameterVector_coe_ae p hp0 hp1 t ht0 ht1,
      pastTail_localTaylor_coe_ae p hp0 hp1 J M hM i t] with x hsub hxK hxT
    calc
      (↑(pastTailParameterVector p hp0 hp1 t ht0 ht1 -
        localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
          (pastTailCenter J) i t) : ℝ → ℝ) x =
        ((↑(pastTailParameterVector p hp0 hp1 t ht0 ht1) : ℝ → ℝ) -
          (↑(localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
            (pastTailCenter J) i t) : ℝ → ℝ)) x := hsub
      _ = pastTailPower p t x - pastTailTaylorPoly p M b t x := by
        rw [Pi.sub_apply, hxK, hxT]
  rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
  calc
    ENNReal.toReal (eLpNorm
      (fun x : ℝ => pastTailPower p t x-pastTailTaylorPoly p M b t x)
      2 (volume.restrict (Set.Ioi 0))) ≤
      ENNReal.toReal (ENNReal.ofReal ((1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^M)) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^M := by
      have hb : 0 < 1-2*p := by linarith
      have hC : 0 ≤ (1-2*p)^(-1/2:ℝ) * (1/2:ℝ)^M :=
        mul_nonneg (Real.rpow_nonneg hb.le _) (pow_nonneg (by norm_num) _)
      rw [ENNReal.toReal_ofReal hC]

def actualPastTailSpan (p : ℝ) (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2)
    (J M : ℕ) : Submodule ℝ PastL2 :=
  pastTailTaylorSpan J M (fun i k => pastTailCoeffVector p hp0 hp1 i k)

/-- Pointwise finite-span approximation of the actual MvN past-tail source
kernel. The only residual inputs are the explicitly proved local Taylor bound
and the exact source-dilation bound for the unallocated near-zero piece. -/
theorem exists_actual_pastTail_approximation
    (p : ℝ) (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2)
    (J M : ℕ) (hM : 0 < M) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ u ∈ actualPastTailSpan p hp0 hp1 J M,
      ‖pastTailParameterVector p hp0 hp1 t ht0 ht1-u‖ ≤
        (1-2*p)^(-1/2:ℝ)*(1/2:ℝ)^M +
          (1/(2:ℝ)^J)^(p+1/2) *
            ‖(pastTailPower_memLp_two hp0 hp1 (by norm_num) (by norm_num)).toLp
              (pastTailPower p 1)‖ := by
  let I := Option (Fin J) × Fin 4
  let v : I → Fin M → PastL2 := fun i k =>
    pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val
  let center : I → ℝ := pastTailCenter J
  let weight : I → ℝ → ℝ := refinedWeight J
  let rem : ℝ → ℝ := fun t => 1-cutoff (t*(2:ℝ)^J)
  let q := pastTailParameterVector p hp0 hp1 t ht0 ht1
  let K : ℝ → PastL2 := fun _ => q
  let δ : ℝ := (1-2*p)^(-1/2:ℝ)*(1/2:ℝ)^M
  let η : ℝ := (1/(2:ℝ)^J)^(p+1/2) *
    ‖(pastTailPower_memLp_two hp0 hp1 (by norm_num) (by norm_num)).toLp
      (pastTailPower p 1)‖
  have hpbase : 0 < 1-2*p := by linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hweights : ∀ i, 0 ≤ weight i t := fun i => refinedWeight_nonneg ht0 i
  have hrem : 0 ≤ rem t := remainder_nonneg J t
  have hmass : (∑ i : I, weight i t)+rem t=1 := refinedMass_eq_one J ht0 ht1
  have hlocal : ∀ i, weight i t ≠ 0 →
      ‖K t-localTaylor M v center i t‖ ≤ δ := by
    intro i hwi
    change ‖pastTailParameterVector p hp0 hp1 t ht0 ht1 -
      localTaylor M (fun i k => pastTailCoeffVector p hp0 hp1 (embedIndex J i) k.val)
        (pastTailCenter J) i t‖ ≤
      (1-2*p)^(-1/2:ℝ)*(1/2:ℝ)^M
    exact pastTail_localTaylor_error_norm_le p hp0 hp1 J M hM i ht0 ht1 hwi
  have htail : rem t ≠ 0 → ‖K t‖ ≤ η := by
    intro hremnz
    have htsmall := remainder_support ht0 ht1 hremnz
    have hscale := AlignmentFractionalPastTailScaling.pastTail_toLp_norm_le
      p hp0 hp1 ht0 ht1 htsmall (by positivity)
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae
      (pastTailParameterVector_coe_ae p hp0 hp1 t ht0 ht1)]
    simpa [η] using hscale
  let u := weightedTaylorCandidate M v center weight t
  have hvspan : taylorSpan M v ≤ actualPastTailSpan p hp0 hp1 J M := by
    unfold taylorSpan actualPastTailSpan pastTailTaylorSpan
    apply Submodule.span_mono
    rintro z ⟨⟨i,k⟩, rfl⟩
    exact ⟨ULift.up (i,k), rfl⟩
  have hu : u ∈ actualPastTailSpan p hp0 hp1 J M :=
    hvspan (weightedTaylorCandidate_mem_taylorSpan M v center weight t)
  have he := weightedTaylorCandidate_error M v center weight rem K
    hδ hη hweights hrem hmass hlocal htail
  refine ⟨u, hu, ?_⟩
  simpa [u, actualPastTailSpan, δ, η, K, q, v, center, weight, rem] using he

theorem actualPastTailSpan_rank_le (p : ℝ) (hp0 : -(1/2:ℝ) < p)
    (hp1 : p < 1/2) (J M : ℕ) :
    Module.rank ℝ (actualPastTailSpan p hp0 hp1 J M) ≤
      (((4*(J+1))*M : ℕ) : Cardinal) := by
  change Module.rank ℝ (pastTailTaylorSpan J M
    (fun i k => pastTailCoeffVector p hp0 hp1 i k)) ≤ _
  exact pastTailTaylorSpan_rank_le J M (fun i k => pastTailCoeffVector p hp0 hp1 i k)

/-- The dyadic specialization has exponentially bounded dimension. -/
theorem actualPastTailSpan_dyadic_rank_bound
    (p : ℝ) (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) :
    ∃ A : ℕ, 0 < A ∧ ∀ n : ℕ,
      Module.rank ℝ (actualPastTailSpan p hp0 hp1 n (n+1)) ≤
        (((A*2^n : ℕ) : Cardinal)) := by
  classical
  let B : ℝ := polynomialBudget (1/2) 2
  let A : ℕ := Nat.ceil (4*B)+1
  have hsum := summable_polynomial_geometric (q:= (1/2:ℝ)) (by norm_num) (by norm_num) 2
  have hApos : 0 < A := by dsimp [A]; omega
  refine ⟨A,hApos,?_⟩
  intro n
  have hpoly : (((n+1:ℕ):ℝ)^2)*(1/2:ℝ)^n ≤ B := by
    dsimp [B, polynomialBudget]
    exact hsum.le_tsum n (fun j hj => by positivity)
  have hA : 4*B ≤ (A:ℝ) := by
    dsimp [A]
    have hc := Nat.le_ceil (4*B)
    push_cast at hc ⊢
    linarith
  have hdimReal : 4*((n+1:ℕ):ℝ)^2 ≤ (A:ℝ)*(2:ℝ)^n := by
    have hn : 0 < (2:ℝ)^n := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hpoly (le_of_lt hn)
    have hinv : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      4*((n+1:ℕ):ℝ)^2 ≤ 4*B*(2:ℝ)^n := by
        nlinarith [hscaled]
      _ ≤ (A:ℝ)*(2:ℝ)^n := by
        exact mul_le_mul_of_nonneg_right hA (by positivity)
  have hdimCast : 4*((n+1:ℕ):ℝ)*((n+1:ℕ):ℝ) ≤ (A:ℝ)*(2:ℝ)^n := by
    calc
      _ = 4*(((n+1:ℕ):ℝ)*((n+1:ℕ):ℝ)) := by ring
      _ ≤ _ := by nlinarith [hdimReal]
  have hdimNat : 4*(n+1)*(n+1) ≤ A*2^n := by exact_mod_cast hdimCast
  have hrank := actualPastTailSpan_rank_le p hp0 hp1 n (n+1)
  calc
    Module.rank ℝ (actualPastTailSpan p hp0 hp1 n (n+1)) ≤
        (((4*(n+1)*(n+1):ℕ):Cardinal)) := by
          simpa [Nat.mul_assoc] using hrank
    _ ≤ (((A*2^n:ℕ):Cardinal)) := by exact_mod_cast hdimNat

/-- The permanent Haar/Taylor span gives the actual dyadic source approximation
with the sharp fractional exponent. -/
theorem exists_actualPastTail_dyadic_approximation
    (p : ℝ) (hp0 : -(1/2:ℝ) < p) (hp1 : p < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ t : ℝ, ∀ ht0 : 0 ≤ t, ∀ ht1 : t ≤ 1,
      ∃ u ∈ actualPastTailSpan p hp0 hp1 n (n+1),
        ‖pastTailParameterVector p hp0 hp1 t ht0 ht1 - u‖ ≤
          C*(2:ℝ)^(-(p+1/2)*n) := by
  let H : ℝ := p+1/2
  let Cδ : ℝ := (1-2*p)^(-1/2:ℝ)
  let N1 : ℝ := ‖(pastTailPower_memLp_two hp0 hp1 (by norm_num) (by norm_num)).toLp
    (pastTailPower p 1)‖
  let C : ℝ := Cδ+N1
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hHlt : H < 1 := by dsimp [H]; linarith
  have hCδ : 0 < Cδ := by
    dsimp [Cδ]
    have hbase : 0 < 1-2*p := by linarith
    positivity
  have hN1 : 0 ≤ N1 := by dsimp [N1]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro n t ht0 ht1
  obtain ⟨u,hu,huerr⟩ := exists_actual_pastTail_approximation p hp0 hp1 n (n+1)
    (by omega) t ht0 ht1
  refine ⟨u,hu,?_⟩
  have hdelta : (1-2*p)^(-1/2:ℝ)*(1/2:ℝ)^(n+1) ≤
      Cδ*(2:ℝ)^(-H*n) := by
    have hexp : -((n:ℝ)+1) ≤ -H*n := by
      have hn : 0 ≤ (n:ℝ) := by positivity
      dsimp [H]
      nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 1-H ≥ 0)) hn]
    have hpw : (1/2:ℝ)^(n+1) ≤ (2:ℝ)^(-H*n) := by
      have hleft : (1/2:ℝ)^(n+1) = (2:ℝ)^(-((n:ℝ)+1)) := by
        rw [← Real.rpow_natCast (1/2:ℝ) (n+1)]
        rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num]
        rw [Real.inv_rpow (by norm_num : 0 ≤ (2:ℝ))]
        rw [Real.rpow_natCast]
        rw [Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
        have hcast : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by norm_num
        rw [← hcast, Real.rpow_natCast]
      rw [hleft]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) hexp
    dsimp [Cδ]
    exact mul_le_mul_of_nonneg_left hpw (by positivity)
  have heta : (1/(2:ℝ)^n)^H*N1 ≤ (2:ℝ)^(-H*n)*N1 := by
    have heq : (1/(2:ℝ)^n)^H = (2:ℝ)^(-H*n) := by
      rw [one_div]
      change ((2:ℝ)^n)⁻¹ ^ H = (2:ℝ)^(-H*n)
      rw [Real.inv_rpow (by positivity : 0 ≤ (2:ℝ)^n)]
      rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2:ℝ)) n H]
      have hneg : -H*(n:ℝ) = -(n*H) := by ring
      rw [hneg, Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
    rw [heq]
  calc
    ‖pastTailParameterVector p hp0 hp1 t ht0 ht1-u‖ ≤
        (1-2*p)^(-1/2:ℝ)*(1/2:ℝ)^(n+1)+(1/(2:ℝ)^n)^H*N1 := by
          simpa [H,N1] using huerr
    _ ≤ C*(2:ℝ)^(-H*n) := by
      dsimp [C]
      nlinarith [hdelta, heta]

end BrownianSharp.AlignmentExponentialPastTailApprox
