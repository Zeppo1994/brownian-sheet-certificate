import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentIsometricEntropy
import Mathlib.Data.Nat.Log

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentCarlEntropyUpper
open BrownianSharp.AlignmentPeriodicWidth
open BrownianSharp.AlignmentWidthRates

/-- A sharp width upper rate supplies the same entropy upper rate on a
fixed multiple of the dyadic indices, at every positive decay exponent. -/
theorem entropy_upper_at_dyadic_indices
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (s a R C : ℝ) (hs : 0<s) (ha : 0≤a)
    (hR : 0≤R) (hC : 0<C) (m₀ : ℕ) (hm₀ : 2≤m₀)
    (hzero : HaarQuarter.TheoremD.Width.kolmogorovWidth K 0≤ENNReal.ofReal R)
    (hupper : ∀k,m₀≤k → HaarQuarter.TheoremD.Width.kolmogorovWidth K k≤
      ENNReal.ofReal (C*logarithmicIndexRate s a k)) :
    ∃ D : ℕ, 0<D ∧ ∃ B : ℝ,0<B ∧
      ∀L : ℕ, 2≤L → m₀≤2^L →
        HaarQuarter.TheoremD.entropyNumber (D*2^L+1) K≤
          ENNReal.ofReal (B*logarithmicIndexRate s a (2^L)) := by
  let A : ℕ := ⌈s⌉₊+1
  let q : ℕ := A+1
  let J : ℝ := (2:ℝ)^(A+1)+2
  let D₀ : ℝ := R*(m₀:ℝ)^A+((2:ℝ)^A+1)*C
  have hsA : s<(A:ℝ) := by
    have h := Nat.le_ceil s
    dsimp [A]
    push_cast
    linarith
  have hJ : 0<J := by dsimp [J]; positivity
  have hD₀ : 0<D₀ := by dsimp [D₀]; positivity
  refine ⟨96*q,by dsimp [q]; omega,J*D₀,mul_pos hJ hD₀,?_⟩
  intro L hL hmN
  let N : ℝ := (2:ℝ)^L
  have hNpos : 0<N := by dsimp [N]; positivity
  have hN1 : 1≤N := by dsimp [N]; exact one_le_pow₀ (by norm_num)
  have hN4 : 4≤N := by
    dsimp [N]
    calc
      4=(2:ℝ)^2 := by norm_num
      _≤(2:ℝ)^L := pow_le_pow_right₀ (by norm_num) hL
  have hlog : 1≤Real.log N := by
    rw [←Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (Real.exp_one_lt_three.le.trans (by linarith))
  have hlogpow : 1≤(Real.log N)^a := by
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hlog ha
  have hβ : 0≤(A:ℝ)-s := by linarith
  have hNβ : 1≤N^((A:ℝ)-s) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hN1 hβ
  have hfactor : N^A*N^(-s)=N^((A:ℝ)-s) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hNpos]
    congr 1
  obtain ⟨B,hB,hBpos,hwidth⟩ := dyadic_width_budget_of_rate_upper_A K ha A hsA
    hm₀ hmN (le_refl (2^L)) (by omega) R C hR hC hzero
    (by intro k hk; simpa only [rate,logarithmicIndexRate] using hupper k hk)
  obtain ⟨P,_,hcover⟩ := entropy_cover_of_Q_dyadic_width_bound
    K A q L (by dsimp [q]; omega) hBpos hwidth
  have hw := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper (2^L) hmN)
  have hrate0 : 0≤C*logarithmicIndexRate s a (2^L) :=
    mul_nonneg hC.le (logarithmicIndexRate_nonneg s a _)
  rw [ENNReal.toReal_ofReal hrate0] at hw
  have hw' : (HaarQuarter.TheoremD.Width.kolmogorovWidth K (2^L)).toReal≤
      C*N^(-s)*(Real.log N)^a := by
    simpa only [logarithmicIndexRate,Nat.cast_pow,Nat.cast_ofNat,N,mul_assoc] using hw
  have hweight : scaleWeightA A s m₀ (2^L)=N^((A:ℝ)-s) := by
    simp only [scaleWeightA,hsA.le,ite_true,Nat.cast_pow,Nat.cast_ofNat,N]
  have hBbound : B≤D₀*N^((A:ℝ)-s)*(Real.log N)^a := by
    rw [hB,hweight]
    have hbase : R*(m₀:ℝ)^A≤R*(m₀:ℝ)^A*N^((A:ℝ)-s)*(Real.log N)^a := by
      have hp : 1≤N^((A:ℝ)-s)*(Real.log N)^a := by nlinarith [mul_le_mul_of_nonneg_left hlogpow (show 0≤N^((A:ℝ)-s) by positivity)]
      have hh := mul_le_mul_of_nonneg_left hp (show 0≤R*(m₀:ℝ)^A by positivity)
      nlinarith [hh]
    have hlast := mul_le_mul_of_nonneg_left hw' (show 0≤N^A by positivity)
    have hlast' : N^A*(HaarQuarter.TheoremD.Width.kolmogorovWidth K (2^L)).toReal≤
      C*N^((A:ℝ)-s)*(Real.log N)^a := by
      calc
        _≤N^A*(C*N^(-s)*(Real.log N)^a) := hlast
        _=C*N^((A:ℝ)-s)*(Real.log N)^a := by rw [←hfactor]; ring
    have heq : (2^L:ℝ)=N := rfl
    change R*(m₀:ℝ)^A+(2:ℝ)^A*C*N^((A:ℝ)-s)*(Real.log N)^a+
      N^A*(HaarQuarter.TheoremD.Width.kolmogorovWidth K (2^L)).toReal≤_
    dsimp [D₀]
    nlinarith [hbase,hlast']
  have hden : (2:ℝ)^(A*L)=N^A := by dsimp [N]; rw [←pow_mul]; congr 1; exact Nat.mul_comm A L
  have hrad : ((2:ℝ)^(A+1)+2)*B/(2:ℝ)^(A*L)≤
      (J*D₀)*logarithmicIndexRate s a (2^L) := by
    rw [hden]
    change J*B/N^A≤_
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBbound hJ.le)
      (show 0≤N^A by positivity)
    calc
      _≤J*(D₀*N^((A:ℝ)-s)*(Real.log N)^a)/N^A := hb
      _=(J*D₀)*logarithmicIndexRate s a (2^L) := by
        rw [←hfactor]
        simp only [logarithmicIndexRate,Nat.cast_pow,Nat.cast_ofNat]
        change _=(J*D₀)*(N^(-s)*(Real.log N)^a)
        field_simp
  exact hcover.trans (ENNReal.ofReal_le_ofReal hrad)

end BrownianSharp.AlignmentCarlEntropyUpper
