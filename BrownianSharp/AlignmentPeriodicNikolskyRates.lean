import BrownianSharp.AlignmentExponentialNikolskyWidth
import BrownianSharp.AlignmentPeriodicWidthUniformUpper

/-! Outer numeric closure for the Nikolsky-2 dyadic width construction. -/
noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPeriodicNikolskyRates

open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.AlignmentPeriodicWidthUniformUpper
open BrownianSharp.AlignmentExponentialNikolskyWidth
open BrownianSharp.AlignmentEndpointWidthExtraction
open HaarQuarter.TheoremD.Width
open BrownianSharp.SmoothResolution BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly

set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

def periodicNikolskyProfile (M T D : ℕ) (q : ℝ) (j : Fin (T+1)) : ℕ :=
  if M ≤ j.val then rank q D (j.val-M)+1 else 1

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : 1≤2^n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      calc
        n+1 ≤ 2^n+1 := Nat.add_le_add_right ih 1
        _ ≤ 2^n+2^n := Nat.add_le_add_left hpow (2^n)
        _ = 2^(n+1) := by rw [pow_succ]; omega

theorem periodic_nikolsky_rank_profile_bound
    {d CT : ℕ} (hd : 2≤d) (hCT : 0<CT) {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ A : ℕ, 0<A ∧ ∀ n : ℕ,
      2*5^d*(n+2)^(d-1)*2^(n+1)*Nat.ceil (1+(1-(3/4:ℝ))⁻¹) +
        ∑ j : Fin (CT*(n+1)+1),
          periodicNikolskyProfile (n+1) (CT*(n+1))
            (2^(n+1)*(n+2)^(d-1)) q j * Nat.ceil (1+(1-q)⁻¹) ≤
          A*Fintype.card (LayerIndex d n) := by
  classical
  let G : ℕ := Nat.ceil (1+(1-q)⁻¹)
  let P : ℕ := Nat.ceil (1+(1-(3/4:ℝ))⁻¹)
  let C : ℝ := 2*5^d*5 + (G:ℝ)*((1-q)⁻¹+(CT+1:ℕ))
  let A : ℕ := Nat.ceil (C*2^d*Nat.factorial (d-1))
  have hG : 0<G := by
    dsimp [G]
    apply Nat.ceil_pos.mpr
    have : 0<(1-q)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hP : P=5 := by norm_num [P]
  have hC : 0<C := by
    dsimp [C]
    have hCT : 0≤((CT+1:ℕ):ℝ) := by positivity
    have hden : 0<1-q := by linarith
    positivity
  have hA : 0<A := by
    dsimp [A]
    apply Nat.ceil_pos.mpr
    have hdpos : 0<(Nat.factorial (d-1):ℝ) := by positivity
    positivity
  refine ⟨A,hA,?_⟩
  intro n
  let M : ℕ := n+1
  let T : ℕ := CT*M
  let D : ℕ := 2^M*(M+1)^(d-1)
  have hMpos : 0<M := by dsimp [M]; omega
  have hMle : M≤T+1 := by
    have hCT1 : 1≤CT := by omega
    have hmul : M≤CT*M := by simpa using Nat.mul_le_mul_right M hCT1
    dsimp [T]
    omega
  have hDcast : (D:ℝ)=(2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1) := by
    dsimp [D]
    norm_cast
  have hDge : (M:ℝ)≤(D:ℝ) := by
    have hpow : (M:ℝ)≤(2:ℝ)^M := by exact_mod_cast nat_le_two_pow M
    have hbase : (1:ℝ)≤((M+1:ℕ):ℝ) := by norm_cast; omega
    have hp : 1≤((M+1:ℕ):ℝ)^(d-1) := one_le_pow₀ hbase
    calc
      (M:ℝ) ≤ (2:ℝ)^M := hpow
      _ = (2:ℝ)^M*1 := by ring
      _ ≤ (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (D:ℝ) := hDcast.symm
  have hprofile := AlignmentExponentialNikolskyWidth.shifted_rank_profile_sum_bound
    (M:=M) (T:=T) (D:=D) hMle hq hq1
  have hT : (T+1:ℝ)≤((CT+1:ℕ):ℝ)*(D:ℝ) := by
    have hMleD : (M:ℝ)≤(D:ℝ) := hDge
    have hCT : 0≤(CT:ℝ) := by positivity
    have hDone : 1≤(D:ℝ) := by
      have hM1 : (1:ℝ)≤(M:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
      linarith [hDge]
    have hprod := mul_le_mul_of_nonneg_left hMleD hCT
    have hTcast : (T:ℝ)=(CT:ℝ)*(M:ℝ) := by dsimp [T]; push_cast; ring
    have hCTcast : ((CT+1:ℕ):ℝ)=(CT:ℝ)+1 := by norm_cast
    rw [Nat.cast_add,Nat.cast_one,hTcast]
    calc
      (CT:ℝ)*(M:ℝ)+1 ≤ (CT:ℝ)*(D:ℝ)+(D:ℝ) := by nlinarith [hprod,hDone]
      _ = ((CT:ℝ)+1)*(D:ℝ) := by ring
  have hsumD :
      (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j:ℝ) ≤
        ((1-q)⁻¹+((CT+1:ℕ):ℝ))*(D:ℝ) := by
    have hprof :
        (∑ j : Fin (T+1), (periodicNikolskyProfile M T D q j:ℝ)) ≤
          (M:ℝ)+(D:ℝ)/(1-q)+((T:ℝ)+1-(M:ℝ)) := by
      have hp := hprofile
      rw [Nat.cast_sum] at hp
      simpa only [periodicNikolskyProfile, Nat.cast_add,Nat.cast_one,
        Nat.cast_sub hMle] using hp
    calc
      _ ≤ (D:ℝ)/(1-q)+(T+1:ℝ) := by
        linarith [hprof]
      _ ≤ (D:ℝ)/(1-q)+((CT+1:ℕ):ℝ)*(D:ℝ) := by linarith [hT]
      _ = _ := by ring
  have hlowG :
      (2*5^d*(n+2)^(d-1)*2^(n+1)*P:ℕ) ≤
        (2*5^d*5:ℕ)*D := by
    rw [hP]
    dsimp [D,M]
    apply le_of_eq
    ring
  have hhighG :
      (∑ j : Fin (T+1), (periodicNikolskyProfile M T D q j:ℝ)*(G:ℝ)) ≤
        (G:ℝ)*((1-q)⁻¹+((CT+1:ℕ):ℝ))*(D:ℝ) := by
    calc
      _ = (∑ j : Fin (T+1), (periodicNikolskyProfile M T D q j:ℝ))*(G:ℝ) := by
        rw [Finset.sum_mul]
      _ ≤ ((1-q)⁻¹+((CT+1:ℕ):ℝ))*(D:ℝ)*(G:ℝ) :=
        mul_le_mul_of_nonneg_right hsumD (by positivity)
      _ = _ := by ring
  have htotal :
      (2*5^d*(n+2)^(d-1)*2^(n+1)*P:ℕ) +
        ∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G ≤
        A*Fintype.card (LayerIndex d n) := by
    have hbase : (D:ℝ) ≤ (2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) := by
      rw [hDcast]
      have hpoly : ((n+2:ℕ):ℝ) ≤ 2*((n+1:ℕ):ℝ) := by
        exact_mod_cast (show n+2≤2*(n+1) by omega)
      have hp := pow_le_pow_left₀ (by positivity : 0≤((n+2:ℕ):ℝ)) hpoly (d-1)
      have hpow : (2:ℝ)^(n+1)=2*(2:ℝ)^n := by rw [pow_succ]; ring
      rw [hpow]
      calc
        _ = 2*(2:ℝ)^n*((n+2:ℕ):ℝ)^(d-1) := by ring
        _ ≤ 2*(2:ℝ)^n*(2*((n+1:ℕ):ℝ))^(d-1) := by gcongr
        _ = (2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) := by
          rw [mul_pow]
          have hdexp : (d-1)+1=d := by omega
          rw [← hdexp, pow_succ]
          have hdeq : 1+(d-1)-1=d-1 := by omega
          have hdeq' : (d-1)+1-1=d-1 := by omega
          rw [hdeq']
          ring
    have hcoef : C*(D:ℝ) ≤ C*(2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) := by
      calc
        C*(D:ℝ) ≤ C*((2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1)) :=
          mul_le_mul_of_nonneg_left hbase (show 0≤C by linarith)
        _ = C*(2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) := by ring
    have hrankLower := periodic_sobolev_rank_le_layer_index (n:=n) hd (G:=1) (by omega)
    have hcardLower :
        (2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) ≤
          (Nat.factorial (d-1):ℝ)*(Fintype.card (LayerIndex d n):ℕ) := by
      have hx := hrankLower
      have hxR : (2:ℝ)*5^d*((n+1:ℕ):ℝ)^(d-1)*(2:ℝ)^n ≤
          (2:ℝ)*5^d*(Nat.factorial (d-1):ℝ)*(Fintype.card (LayerIndex d n):ℕ) := by
        have hxR0 : (2:ℝ)*5^d*((n+1:ℕ):ℝ)^(d-1)*(2:ℝ)^n*1 ≤
            (2:ℝ)*5^d*(Nat.factorial (d-1):ℝ)*1*
              (Fintype.card (LayerIndex d n):ℕ) := by exact_mod_cast hx
        simpa using hxR0
      have hc : 0<(2:ℝ)*5^d := by positivity
      have hxR' : ((2:ℝ)*5^d)*((2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1)) ≤
          ((2:ℝ)*5^d)*((Nat.factorial (d-1):ℝ)*
            (Fintype.card (LayerIndex d n):ℕ)) := by
        calc
          _ = (2:ℝ)*5^d*((n+1:ℕ):ℝ)^(d-1)*(2:ℝ)^n := by ring
          _ ≤ (2:ℝ)*5^d*(Nat.factorial (d-1):ℝ)*
              (Fintype.card (LayerIndex d n):ℕ) := hxR
          _ = _ := by ring
      exact (mul_le_mul_iff_of_pos_left hc).mp hxR'
    have hceilA : C*(2:ℝ)^d*(Nat.factorial (d-1):ℝ) ≤ (A:ℝ) := by
      dsimp [A]
      exact_mod_cast Nat.le_ceil _
    have hcoefCard : C*(D:ℝ) ≤ (A:ℝ)*(Fintype.card (LayerIndex d n):ℕ) := by
      calc
        _ ≤ C*(2:ℝ)^d*(2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1) := hcoef
        _ ≤ C*(2:ℝ)^d*(Nat.factorial (d-1):ℝ)*
            (Fintype.card (LayerIndex d n):ℕ) := by
          calc
            _ = (C*(2:ℝ)^d)*((2:ℝ)^n*((n+1:ℕ):ℝ)^(d-1)) := by ring
            _ ≤ (C*(2:ℝ)^d)*((Nat.factorial (d-1):ℝ)*
                (Fintype.card (LayerIndex d n):ℕ)) :=
              mul_le_mul_of_nonneg_left hcardLower (by positivity)
            _ = _ := by ring
        _ ≤ (A:ℝ)*(Fintype.card (LayerIndex d n):ℕ) := by
          exact mul_le_mul_of_nonneg_right hceilA (by positivity)
    have hsumfinal :
        (2:ℝ)*5^d*5*(D:ℝ) +
          (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G:ℝ) ≤ C*(D:ℝ) := by
      dsimp [C]
      rw [mul_add]
      nlinarith [hhighG]
    have hlowCast :
        ((2*5^d*(n+2)^(d-1)*2^(n+1)*P:ℕ):ℝ) ≤
          (2:ℝ)*5^d*5*(D:ℝ) := by exact_mod_cast hlowG
    have hcombine :
        ((2*5^d*(n+2)^(d-1)*2^(n+1)*P:ℕ):ℝ) +
          (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G:ℝ) ≤ C*(D:ℝ) := by
      calc
        _ ≤ (2:ℝ)*5^d*5*(D:ℝ) +
            (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G:ℝ) :=
          by
            simpa [add_comm] using add_le_add_right hlowCast
              (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G:ℝ)
        _ ≤ C*(D:ℝ) := hsumfinal
    have hfrom :
        ((2*5^d*(n+2)^(d-1)*2^(n+1)*P:ℕ):ℝ) +
          (∑ j : Fin (T+1), periodicNikolskyProfile M T D q j*G:ℝ) ≤
          (A:ℝ)*(Fintype.card (LayerIndex d n):ℕ) := hcombine.trans hcoefCard
    exact_mod_cast hfrom
  simpa [G,P,M,T,D,periodicNikolskyProfile] using htotal

private theorem periodic_nikolsky_rho_power_ratio {r : ℝ} (n : ℕ) :
    ((2:ℝ)^(1-2*r))^n/(2:ℝ)^n=(2:ℝ)^(-2*r*(n:ℝ)) := by
  have hnum : ((2:ℝ)^(1-2*r))^n=(2:ℝ)^((1-2*r)*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have hden : (2:ℝ)^n=(2:ℝ)^(n:ℝ) := (Real.rpow_natCast (2:ℝ) n).symm
  rw [hnum,hden,div_eq_mul_inv]
  rw [← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  push_cast
  ring

/-- The actual Nikolsky-2 finite Fourier construction has its sharp dyadic
upper rate. The parameters are chosen uniformly in the layer index; all
Fourier tail, grid, and allocated KGG errors are discharged here. -/
theorem periodic_nikolsky_dyadic_width_upper
    {d : ℕ} (hd : 2≤d) {r : ℝ} (hr : 1/2<r) :
    ∃ A : ℕ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ n : ℕ,
      kolmogorovWidth {f : RealPeriodic d | NikolskyUnitBall (2:ENNReal) r f}
        (A*Fintype.card (LayerIndex d n)) ≤
        ENNReal.ofReal (B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2)) := by
  classical
  obtain ⟨q',CT,hq'lo,hq'hi,hCTpos,hCT⟩ :=
    AlignmentPeriodicWidthUniformUpper.exists_periodic_tail_cutoff hr
  obtain ⟨K,hK,hKC⟩ := AlignmentTorusSampling.exists_sampling_integer d
  let ρ : ℝ := (2:ℝ)^(1-2*r)
  let q : ℝ := (1+ρ)/2
  let G : ℕ := Nat.ceil (1+(1-q)⁻¹)
  let P : ℕ := Nat.ceil (1+(1-(3/4:ℝ))⁻¹)
  let CH : ℕ := Nat.ceil r+d+3
  let L : ℝ := Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
      (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*Real.log 2
  let tailCoeff : ℝ := Real.sqrt ((5:ℝ)^d) *
      ∑' s : Fin d → ℕ, q'^(∑ i,s i)
  let stochCoeff : ℝ := Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
      polynomialBudget (ρ/q) (d-1)) *
      (2:ℝ)^((d:ℝ)/2) * polynomialBudget (Real.sqrt (ρ/q)) (d-1)
  let B : ℝ := tailCoeff+(CT+1:ℕ)^d+2^d+stochCoeff
  have hρpos : 0<ρ := by dsimp [ρ]; positivity
  have hρone : ρ<1 := by
    dsimp [ρ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hqρ : ρ<q := by dsimp [q]; linarith
  have hqpos : 0<q := by dsimp [q]; linarith
  have hqone : q<1 := by dsimp [q]; linarith
  have hq'pos : 0<q' := by
    have hq0 : 0<(2:ℝ)^(1/2-r) := Real.rpow_pos_of_pos (by norm_num) _
    exact hq0.trans hq'lo
  obtain ⟨A,hApos,hboundAll⟩ := periodic_nikolsky_rank_profile_bound hd hCTpos hqpos hqone
  have hLpos : 0<L := by
    dsimp [L]
    have hlog4 : 0<Real.log 4 := Real.log_pos (by norm_num)
    have hlogK : 0≤Real.log ((K:ℝ)+1) := Real.log_nonneg (by norm_cast; omega)
    have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hbudgetρ : 0≤polynomialBudget (ρ/q) (d-1) :=
    polynomialBudget_nonneg (by positivity) _
  have hbudgetq : 0≤polynomialBudget (Real.sqrt (ρ/q)) (d-1) :=
    polynomialBudget_nonneg (Real.sqrt_nonneg _) _
  have htailnonneg : 0≤tailCoeff := by
    dsimp [tailCoeff]
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply tsum_nonneg
    intro s
    exact pow_nonneg hq'pos.le _
  have hstochNonneg : 0≤stochCoeff := by dsimp [stochCoeff]; positivity
  have hBpos : 0<B := by dsimp [B]; positivity
  refine ⟨A,hApos,B,hBpos,?_⟩
  intro n
  let M : ℕ := n+1
  let T : ℕ := CT*M
  let H : ℕ := CH*M
  let D0 : ℕ := 2^M*(M+1)^(d-1)
  let D : Fin (T+1)→ℕ := fun j => periodicNikolskyProfile M T D0 q j
  let lam : ℝ := (2:ℝ)^(-r*(M:ℝ))
  let gridLog : ℝ := Real.log (2*(Fintype.card
      (Fin d→Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ)+2)
  have hMpos : 0<M := by dsimp [M]; omega
  have hCTone : 1≤CT := by omega
  have hMT : M≤T+1 := by
    have hmul : M≤CT*M := by simpa using Nat.mul_le_mul_right M hCTone
    dsimp [T]
    omega
  have hρeq : ρ=(2:ℝ)^(1-2*r) := rfl
  have hρpow : ρ^M/(2:ℝ)^M=lam^2 := by
    dsimp [lam]
    rw [show ρ=(2:ℝ)^(1-2*r) by rfl, periodic_nikolsky_rho_power_ratio]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    push_cast
    ring
  have hDpos : ∀ j, 0<D j := by
    intro j
    by_cases hj : M≤j.val
    · simp [D,periodicNikolskyProfile,hj]
    · simp [D,periodicNikolskyProfile,hj]
  have hDlower : ∀ j : Fin (T+1), M≤j.val →
      (2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1)*q^(j.val-M)/2 ≤ (D j:ℝ) := by
    intro j hj
    have hh := AlignmentGeometricRanks.half_profile_le_rank_add_one hqpos.le D0 (j.val-M)
    have hcast : (D j:ℝ)=(AlignmentGeometricRanks.rank q D0 (j.val-M):ℝ)+1 := by
      simp [D,periodicNikolskyProfile,hj]
    have hD0cast : (D0:ℝ)=(2:ℝ)^M*((M+1:ℕ):ℝ)^(d-1) := by
      dsimp [D0]
      norm_cast
    simpa [D0,hcast] using hh
  have hGpos : 0<G := by
    dsimp [G]
    apply Nat.ceil_pos.mpr
    have hden : 0<1-q := by linarith
    have hinv : 0<(1-q)⁻¹ := inv_pos.mpr hden
    linarith
  have hP : P=5 := by norm_num [P]
  have hrank :
      2*5^d*(M+1)^(d-1)*2^M*P +
        ∑ j : Fin (T+1), D j*G ≤ A*Fintype.card (LayerIndex d n) := by
    have hbound := hboundAll n
    simpa [M,T,D,D0,G,P,hP,periodicNikolskyProfile] using hbound
  have hlog : 0≤gridLog ∧ gridLog≤L*((M+1:ℕ):ℝ) := by
    have hsize := AlignmentTorusSampling.samplingGridSize_log_card d K T H
    have hlogK : 0≤Real.log ((K:ℝ)+1) := Real.log_nonneg (by norm_cast; omega)
    have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hshape :
        ((d+2)*T+H:ℕ) ≤ ((d+2)*CT+CH:ℕ)*M := by
      dsimp [T,H]
      exact le_of_eq (by ring)
    have hshapeR :
        (((d+2)*T+H:ℕ):ℝ) ≤ (((d+2)*CT+CH:ℕ):ℝ)*(M:ℝ) := by
      exact_mod_cast hshape
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hshapeR (by positivity : (0:ℝ)≤d)) hlog2
    constructor
    · have hconst : 0≤Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1) := by positivity
      have := hsize
      have hbound : 0≤Real.log (2*(Fintype.card
          (Fin d→Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ)+2) :=
        Real.log_nonneg (by
          have hc0 : 0≤(Fintype.card
              (Fin d→Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ) := by positivity
          have hc : (1:ℝ)≤2*(Fintype.card
              (Fin d→Fin (AlignmentTorusSampling.samplingGridSize d K T H+1)):ℝ)+2 := by nlinarith
          exact hc)
      simpa [gridLog] using hbound
    · have hconst : 0≤Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1) := by positivity
      have hM1 : (1:ℝ)≤(M:ℝ)+1 := by norm_cast; omega
      dsimp [gridLog,L]
      calc
        _ ≤ Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
            (d:ℝ)*(((d+2)*T+H:ℕ):ℝ)*Real.log 2 := hsize
        _ ≤ (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
            (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*Real.log 2)*((M+1:ℕ):ℝ) := by
          have hconstle : Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1) ≤
              (Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1))*((M:ℝ)+1) := by
            nlinarith [mul_le_mul_of_nonneg_left hM1 hconst]
          have hcoefM : (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*(M:ℝ)*Real.log 2 ≤
              (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*((M:ℝ)+1)*Real.log 2 := by
            have hc : 0≤(d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith) hc) hlog2
          have hmul' : (d:ℝ)*(((d+2)*T+H:ℕ):ℝ)*Real.log 2 ≤
              (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*(M:ℝ)*Real.log 2 := by
            calc
              _ ≤ (d:ℝ)*((((d+2)*CT+CH:ℕ):ℝ)*(M:ℝ))*Real.log 2 := hmul
              _ = _ := by ring
          calc
            _ ≤ Real.log 4+(d:ℝ)*Real.log ((K:ℝ)+1)+
                (d:ℝ)*(((d+2)*CT+CH:ℕ):ℝ)*(M:ℝ)*Real.log 2 := by
              nlinarith [hmul']
            _ ≤ _ := add_le_add hconstle hcoefM
            _ = _ := by push_cast; ring
  have hCH : (r:ℝ)+(d:ℝ)+3 ≤ (CH:ℝ) := by
    dsimp [CH]
    have hceil : r≤(Nat.ceil r:ℝ) := by exact_mod_cast Nat.le_ceil r
    push_cast
    linarith
  have hH : (r+(d:ℝ)+3)*(M:ℝ) ≤ (H:ℝ) := by
    dsimp [H]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hCH (by positivity)
  have hrpowGrid : lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) =
      (2:ℝ)^(-((r+(d:ℝ)+3)*(M:ℝ))) := by
    dsimp [lam]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hgridDecay : ((2:ℝ)^H)⁻¹ ≤ lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) := by
    have hleft : ((2:ℝ)^H)⁻¹=(2:ℝ)^(-(H:ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [hleft]
    rw [hrpowGrid]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    linarith
  have hMpow : (M:ℝ)^d ≤ (2:ℝ)^((d:ℝ)*(M:ℝ)) := by
    have hnat := nat_le_two_pow M
    have hnatR : (M:ℝ)≤(2:ℝ)^M := by exact_mod_cast hnat
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(M:ℝ)) hnatR d
    calc
      (M:ℝ)^d ≤ ((2:ℝ)^M)^d := hp
      _ = (2:ℝ)^(M*d) := by rw [← pow_mul]
      _ = (2:ℝ)^((M*d:ℕ):ℝ) := by rw [Real.rpow_natCast]
      _ = (2:ℝ)^((d:ℝ)*(M:ℝ)) := by congr 1; push_cast; ring
  have hlowGrid :
      Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ ≤
        (2:ℝ)^d * lam * ((M:ℝ)^((d:ℝ)/2)) := by
    have hMplus : ((M+1:ℕ):ℝ)≤2*(M:ℝ) := by
      have hM1 : 1≤M := by omega
      exact_mod_cast (show M+1≤2*M by omega)
    have hsqrt : Real.sqrt (((M+1:ℕ):ℝ)^d) ≤ ((M+1:ℕ):ℝ)^d := by
      rw [Real.sqrt_le_left (by positivity)]
      have hbase : (1:ℝ)≤((M+1:ℕ):ℝ) := by norm_cast; omega
      have hone : (1:ℝ)≤((M+1:ℕ):ℝ)^d := one_le_pow₀ hbase
      nlinarith [hone]
    have hpoly : ((M+1:ℕ):ℝ)^d ≤ (2:ℝ)^d*(M:ℝ)^d := by
      calc
        _ ≤ (2*(M:ℝ))^d := pow_le_pow_left₀ (by positivity) hMplus d
        _ = _ := by rw [mul_pow]
    have hdecay := hgridDecay
    have hexp : (2:ℝ)^d*(M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) ≤ (2:ℝ)^d := by
      have hpow : (M:ℝ)^d≤(2:ℝ)^((d:ℝ)*(M:ℝ)) := hMpow
      have hexp2 : (2:ℝ)^((d:ℝ)*(M:ℝ))*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) ≤ 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ)≤2)
        have hMnonneg : 0≤(M:ℝ) := by positivity
        nlinarith
      calc
        _ ≤ (2:ℝ)^d*((2:ℝ)^((d:ℝ)*(M:ℝ))*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by
          calc
            _ = (2:ℝ)^d*((M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
        _ ≤ _ := by
          calc
            _ = (2:ℝ)^d*((2:ℝ)^((d:ℝ)*(M:ℝ))*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by ring
            _ ≤ (2:ℝ)^d*1 := mul_le_mul_of_nonneg_left hexp2 (by positivity)
            _ = _ := by ring
    calc
      _ ≤ ((M+1:ℕ):ℝ)^d*((2:ℝ)^H)⁻¹ :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ ((M+1:ℕ):ℝ)^d*lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) := by
        calc
          _ ≤ ((M+1:ℕ):ℝ)^d*(lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) :=
            mul_le_mul_of_nonneg_left hgridDecay (by positivity)
          _ = _ := by ring
      _ ≤ (2:ℝ)^d*(M:ℝ)^d * (2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))*lam := by
        calc
          _ = ((M+1:ℕ):ℝ)^d*lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) := by ring
          _ ≤ ((2:ℝ)^d*(M:ℝ)^d)*lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpoly (by positivity)) (by positivity)
          _ = _ := by ring
      _ ≤ (2:ℝ)^d*lam := by
        calc
          _ = (2:ℝ)^d*lam*((M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by ring
          _ ≤ (2:ℝ)^d*lam*1 := by
            calc
              _ = ((2:ℝ)^d*(M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)))*lam := by ring
              _ ≤ (2:ℝ)^d*lam := mul_le_mul_of_nonneg_right hexp (by positivity)
              _ = _ := by ring
          _ = _ := by ring
      _ ≤ (2:ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) := by
        have hMbase : (1:ℝ)≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
        have hMpowpos : 1≤(M:ℝ)^((d:ℝ)/2) :=
          Real.one_le_rpow hMbase (by positivity)
        calc
          _ = (2:ℝ)^d*lam*1 := by ring
          _ ≤ (2:ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) :=
            mul_le_mul_of_nonneg_left hMpowpos (by positivity)
  have hhighGrid :
      ((2:ℝ)^H)⁻¹ *
        (∑ j : Fin (T+1), if M≤j.val then
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) ≤
        ((CT+1:ℕ):ℝ)^d * lam * ((M:ℝ)^((d:ℝ)/2)) := by
    have hTbound : (T+1:ℝ)≤((CT+1:ℕ):ℝ)*(M:ℝ) := by
      have hCTcast : ((CT+1:ℕ):ℝ)=(CT:ℝ)+1 := by norm_cast
      rw [show (T:ℝ)=(CT:ℝ)*(M:ℝ) by dsimp [T]; push_cast; ring]
      rw [hCTcast]
      have hM1 : (1:ℝ)≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
      nlinarith
    have hsum :
        (∑ j : Fin (T+1), if M≤j.val then
          Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) ≤ (T+1:ℝ)^d := by
      calc
        _ ≤ ∑ j : Fin (T+1), ((T+1:ℕ):ℝ)^(d-1) := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs with h
          · have hj' : ((j.val+1:ℕ):ℝ)≤(T+1:ℝ) := by exact_mod_cast (by omega : j.val+1≤T+1)
            have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤((j.val+1:ℕ):ℝ)) hj' (d-1)
            have hp' : ((j.val+1:ℕ):ℝ)^(d-1) ≤ ((T+1:ℕ):ℝ)^(d-1) := by
              simpa only [Nat.cast_add,Nat.cast_one] using hp
            have hsqrt : Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) ≤ ((j.val+1:ℕ):ℝ)^(d-1) := by
              rw [Real.sqrt_le_left (by positivity)]
              have hbase : (1:ℝ)≤((j.val+1:ℕ):ℝ) := by norm_cast; omega
              have hpowone : (1:ℝ)≤((j.val+1:ℕ):ℝ)^(d-1) := one_le_pow₀ hbase
              nlinarith [hpowone]
            exact hsqrt.trans hp'
          · positivity
        _ = (T+1:ℝ)*(T+1:ℝ)^(d-1) := by simp
        _ = (T+1:ℝ)^(1+(d-1)) := by rw [pow_add]; simp
        _ = _ := by congr 1; omega
    have hrough : (T+1:ℝ)^d ≤ ((CT+1:ℕ):ℝ)^d*(M:ℝ)^d := by
      calc
        _ ≤ (((CT+1:ℕ):ℝ)*(M:ℝ))^d := pow_le_pow_left₀ (by positivity) hTbound d
        _ = ((CT+1:ℕ):ℝ)^d*(M:ℝ)^d := by rw [mul_pow]
    have hMpow := hMpow
    have hdecay := hgridDecay
    have hexp : (M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))≤1 := by
      calc
        _ ≤ (2:ℝ)^((d:ℝ)*(M:ℝ))*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ)) :=
          mul_le_mul_of_nonneg_right hMpow (by positivity)
        _ ≤ 1 := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
          apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ)≤2)
          have hMnonneg : 0≤(M:ℝ) := by positivity
          nlinarith
    calc
      _ ≤ ((2:ℝ)^H)⁻¹*(T+1:ℝ)^d := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ lam*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))*(((CT+1:ℕ):ℝ)^d*(M:ℝ)^d) := by
        apply mul_le_mul hgridDecay hrough (by positivity) (by positivity)
      _ = ((CT+1:ℕ):ℝ)^d*lam*((M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by ring
      _ ≤ ((CT+1:ℕ):ℝ)^d*lam := by
        calc
          _ = ((CT+1:ℕ):ℝ)^d*lam*((M:ℝ)^d*(2:ℝ)^(-((d:ℝ)+3)*(M:ℝ))) := by ring
          _ ≤ ((CT+1:ℕ):ℝ)^d*lam*1 := by
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
          _ = _ := by ring
      _ ≤ ((CT+1:ℕ):ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) := by
        have hMbase : (1:ℝ)≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
        have hMpowpos : 1≤(M:ℝ)^((d:ℝ)/2) := Real.one_le_rpow hMbase (by positivity)
        calc
          _ = ((CT+1:ℕ):ℝ)^d*lam*1 := by ring
          _ ≤ ((CT+1:ℕ):ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) :=
            mul_le_mul_of_nonneg_left hMpowpos (by positivity)
  let tailRatio : ℝ := ((2:ℝ)^(1/2-r))/q'
  let Tail : ℝ := tailCoeff*lam
  have htailRatio0 : 0≤tailRatio := by dsimp [tailRatio]; positivity
  have htailRatio1 : tailRatio≤1 := by
    dsimp [tailRatio]
    exact (div_le_one hq'pos).2 (le_of_lt hq'lo)
  have htailPow : tailRatio^(T+1)≤lam := by
    have hCTcast : (CT:ℝ)=(CT:ℝ) := rfl
    have hpowCT : tailRatio^CT≤(2:ℝ)^(-r) := hCT
    have hpowM := pow_le_pow_left₀ (by positivity : (0:ℝ)≤tailRatio^CT) hpowCT M
    have hpowIdent : (tailRatio^CT)^M=tailRatio^(CT*M) := by rw [pow_mul]
    have hsmallIdent : ((2:ℝ)^(-r))^M=lam := by
      calc
        ((2:ℝ)^(-r))^M = (2:ℝ)^((-r)*(M:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
        _ = lam := by dsimp [lam]
    have hsucc : tailRatio^(CT*M+1)≤tailRatio^(CT*M) := by
      rw [pow_succ]
      calc
        tailRatio^(CT*M)*tailRatio ≤ tailRatio^(CT*M)*1 :=
          mul_le_mul_of_nonneg_left htailRatio1 (pow_nonneg htailRatio0 (CT*M))
        _ = tailRatio^(CT*M) := by ring
    calc
      tailRatio^(T+1) = tailRatio^(CT*M+1) := by simp [T]
      _ ≤ tailRatio^(CT*M) := hsucc
      _ = (tailRatio^CT)^M := hpowIdent.symm
      _ ≤ ((2:ℝ)^(-r))^M := hpowM
      _ = lam := hsmallIdent
  have htailTerm :
      Real.sqrt ((5:ℝ)^d)*tailRatio^(T+1)*
        (∑' s : Fin d→ℕ, q'^(∑ i,s i)) ≤ Tail := by
    dsimp [Tail,tailCoeff]
    calc
      _ ≤ Real.sqrt ((5:ℝ)^d)*lam*
          (∑' s : Fin d→ℕ, q'^(∑ i,s i)) := by gcongr
      _ = _ := by ring
  have htailactual :
      ∀ f : RealPeriodic d, NikolskyUnitBall (2:ENNReal) r f →
        (∑' s : ((periodicShapeSimplex (d:=d) T)ᶜ : Set (Fin d→ℕ)),
          ‖block s.1 f‖) ≤ Tail := by
    intro f hf
    have hgrade : ∀ s : Fin d→ℕ,
        s∉periodicShapeSimplex (d:=d) T → T+1≤∑ i,s i := by
      intro s hs
      by_contra hnot
      have hsum : ∑ i,s i≤T := by omega
      exact hs ((AlignmentPeriodicWidthFeatureAssembly.mem_periodicShapeSimplex s).2 hsum)
    have htail := BrownianSharp.AlignmentPeriodicTail.nikolsky_two_uniform_tail
      (periodicShapeSimplex (d:=d) T) r hr q' hq'lo hq'hi hgrade f hf
    dsimp [Tail,tailCoeff]
    calc
      _ ≤ Real.sqrt ((5:ℝ)^d)*tailRatio^(T+1)*
          (∑' s : Fin d→ℕ, q'^(∑ i,s i)) := by
        simpa [tailRatio] using htail
      _ ≤ Real.sqrt ((5:ℝ)^d)*lam*
          (∑' s : Fin d→ℕ, q'^(∑ i,s i)) := by
        gcongr
      _ = _ := by ring
  have hroot : Real.sqrt (((M+1:ℕ):ℝ)^d) ≤
      (2:ℝ)^((d:ℝ)/2)*(M:ℝ)^((d:ℝ)/2) := by
    have hMplus : ((M+1:ℕ):ℝ)≤2*(M:ℝ) := by
      exact_mod_cast (show M+1≤2*M by omega)
    have hpow : (((M+1:ℕ):ℝ)^d)^(1/2:ℝ) =
        ((M+1:ℕ):ℝ)^((d:ℝ)/2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ)≤((M+1:ℕ):ℝ))]
      congr 1
      push_cast
      field_simp
    rw [Real.sqrt_eq_rpow, hpow]
    calc
      ((M+1:ℕ):ℝ)^((d:ℝ)/2) ≤ (2*(M:ℝ))^((d:ℝ)/2) := by
        exact Real.rpow_le_rpow (by positivity) hMplus (by positivity)
      _ = (2:ℝ)^((d:ℝ)/2)*(M:ℝ)^((d:ℝ)/2) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity : (0:ℝ)≤(M:ℝ))]
  have hstoch :
      Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
          polynomialBudget (ρ/q) (d-1)) * lam *
        Real.sqrt (((M+1:ℕ):ℝ)^d) *
          polynomialBudget (Real.sqrt (ρ/q)) (d-1) ≤
        stochCoeff*lam*((M:ℝ)^((d:ℝ)/2)) := by
    dsimp [stochCoeff]
    have hroot' := hroot
    have hcoef : 0≤Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
          polynomialBudget (ρ/q) (d-1)) := Real.sqrt_nonneg _
    have hpoly : 0≤polynomialBudget (Real.sqrt (ρ/q)) (d-1) := hbudgetq
    calc
      _ ≤ Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
            polynomialBudget (ρ/q) (d-1))*lam*
          ((2:ℝ)^((d:ℝ)/2)*(M:ℝ)^((d:ℝ)/2))*
            polynomialBudget (Real.sqrt (ρ/q)) (d-1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot' (mul_nonneg hcoef (by positivity))) hpoly
      _ = stochCoeff*lam*((M:ℝ)^((d:ℝ)/2)) := by
        dsimp [stochCoeff]
        ring_nf
  have hcomp := periodic_nikolsky_exact_error_components
    (d:=d) (M:=M) (T:=T) (H:=H) (ρ:=ρ) (q:=q) (L:=L) (lam:=lam)
    (G:=gridLog) (Tail:=Tail) hd hMpos hMT hρpos hqpos hqρ hLpos
    (by positivity : 0<lam) hlog.1 hlog.2 hρpow D hDlower
  have herror :
      Real.sqrt ((5:ℝ)^d)*tailRatio^(T+1)*
        (∑' s : Fin d→ℕ, q'^(∑ i,s i))+
        Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹+
        (∑ j : Fin (T+1),
          if (periodicShapeSimplex (d:=d) T).filter
              (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val)=∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1))*
              (((2:ℝ)^H)⁻¹+Real.sqrt ((4*(10000:ℝ)^2*
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val))*gridLog/
                  (D j:ℝ)*polynomialBudget (ρ/q) (d-1)))) ) ≤
        B*lam*((M:ℝ)^((d:ℝ)/2)) := by
    have hMbase : (1:ℝ)≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
    have hMpowpos : 1≤(M:ℝ)^((d:ℝ)/2) := Real.one_le_rpow hMbase (by positivity)
    calc
      _ ≤ Tail+Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹+
          (∑ j : Fin (T+1),
            if (periodicShapeSimplex (d:=d) T).filter
                (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val)=∅ then 0 else
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1))*
                (((2:ℝ)^H)⁻¹+Real.sqrt ((4*(10000:ℝ)^2*
                  (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val))*gridLog/
                    (D j:ℝ)*polynomialBudget (ρ/q) (d-1)))) ) := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right htailTerm
          (Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹+
            (∑ j : Fin (T+1),
              if (periodicShapeSimplex (d:=d) T).filter
                  (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val)=∅ then 0 else
                Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1))*
                  (((2:ℝ)^H)⁻¹+Real.sqrt ((4*(10000:ℝ)^2*
                    (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val))*gridLog/
                      (D j:ℝ)*polynomialBudget (ρ/q) (d-1)))) ))
      _ ≤ Tail+Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹+
          ((2:ℝ)^H)⁻¹ *
            (∑ j : Fin (T+1), if M≤j.val then
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) +
          Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
            polynomialBudget (ρ/q) (d-1))*lam*
            Real.sqrt (((M+1:ℕ):ℝ)^d)*
            polynomialBudget (Real.sqrt (ρ/q)) (d-1) := hcomp
      _ ≤ (tailCoeff+(CT+1:ℕ)^d+2^d+stochCoeff)*lam*((M:ℝ)^((d:ℝ)/2)) := by
        have htailB : Tail≤tailCoeff*lam*((M:ℝ)^((d:ℝ)/2)) := by
          dsimp [Tail]
          calc
            tailCoeff*lam = (tailCoeff*lam)*1 := by ring
            _ ≤ (tailCoeff*lam)*((M:ℝ)^((d:ℝ)/2)) :=
              mul_le_mul_of_nonneg_left hMpowpos (by positivity)
        have hlowB : Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹ ≤
            (2:ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) := hlowGrid
        have hhighB : ((2:ℝ)^H)⁻¹ *
            (∑ j : Fin (T+1), if M≤j.val then
              Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1)) else 0) ≤
            ((CT+1:ℕ):ℝ)^d*lam*((M:ℝ)^((d:ℝ)/2)) := hhighGrid
        have hstochB :
            Real.sqrt (4*(10000:ℝ)^2*(2*(5:ℝ)^d)*2*L*
              polynomialBudget (ρ/q) (d-1))*lam*
              Real.sqrt (((M+1:ℕ):ℝ)^d)*
              polynomialBudget (Real.sqrt (ρ/q)) (d-1) ≤
            stochCoeff*lam*((M:ℝ)^((d:ℝ)/2)) := hstoch
        nlinarith [htailB,hlowB,hhighB,hstochB]
      _ = B*lam*((M:ℝ)^((d:ℝ)/2)) := by dsimp [B]
  have herrorTarget :
      Real.sqrt ((5:ℝ)^d)*((2:ℝ)^(1/2-r)/q')^(T+1)*
        (∑' s : Fin d→ℕ, q'^(∑ i,s i))+
        Real.sqrt (((M+1:ℕ):ℝ)^d)*((2:ℝ)^H)⁻¹+
        (∑ j : Fin (T+1),
          if (periodicShapeSimplex (d:=d) T).filter
              (fun s => M≤∑ k,s k ∧ (∑ k,s k)=j.val)=∅ then 0 else
            Real.sqrt (((j.val+1:ℕ):ℝ)^(d-1))*
              (((2:ℝ)^H)⁻¹+Real.sqrt ((4*(10000:ℝ)^2*
                (2*(5:ℝ)^d*((j.val+1:ℕ):ℝ)^(d-1)*ρ^(j.val))*gridLog/
                  (D j:ℝ)*polynomialBudget (ρ/q) (d-1)))) ) ≤
      B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2) := by
    have hscale : B*lam*((M:ℝ)^((d:ℝ)/2)) ≤
        B*(2:ℝ)^(-r*(n:ℝ))*((n:ℝ)+1)^((d:ℝ)/2) := by
      have hMcast : (M:ℝ)=(n:ℝ)+1 := by simp [M]
      have hfactor : lam=(2:ℝ)^(-r*(n:ℝ))*(2:ℝ)^(-r) := by
        dsimp [lam,M]
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 1
        push_cast
        ring
      have hrpos' : 0<r := by linarith
      have hsmall' : (2:ℝ)^(-r)≤1 := by
        rw [← Real.rpow_zero (2:ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith)
      have hlamle' : lam≤(2:ℝ)^(-r*(n:ℝ)) := by
        calc
          lam = (2:ℝ)^(-r*(n:ℝ))*(2:ℝ)^(-r) := hfactor
          _ ≤ _ := mul_le_mul_of_nonneg_left hsmall' (by positivity)
          _ = _ := by ring
      rw [hMcast]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlamle' (le_of_lt hBpos)) (by positivity)
    calc
      _ ≤ B*lam*((M:ℝ)^((d:ℝ)/2)) := by
        simpa [tailRatio, gridLog] using herror
      _ ≤ _ := hscale
  have hrankwidth := periodic_nikolsky_width_bound_of_parameters
    (d:=d) (M:=M) (T:=T) (H:=H) (K:=K)
    (m:=A*Fintype.card (LayerIndex d n)) hd hMpos hMT r hr
    hρpos hqpos hqone hqρ hρeq hq'lo hq'hi hK hKC D hDpos
    hrank B (by positivity) n herrorTarget
  have hlamle : lam≤(2:ℝ)^(-r*(n:ℝ)) := by
    have hfactor : lam=(2:ℝ)^(-r*(n:ℝ))*(2:ℝ)^(-r) := by
      dsimp [lam,M]
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      push_cast
      ring
    have hrpos : 0<r := by linarith
    have hsmall : (2:ℝ)^(-r)≤1 := by
      rw [← Real.rpow_zero (2:ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith)
    calc
      lam = (2:ℝ)^(-r*(n:ℝ))*(2:ℝ)^(-r) := hfactor
      _ ≤ (2:ℝ)^(-r*(n:ℝ))*1 :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  exact hrankwidth

end BrownianSharp.AlignmentPeriodicNikolskyRates
