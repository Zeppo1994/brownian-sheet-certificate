import BrownianSharp.AlignmentGaussianChaining
import BrownianSharp.AlignmentExponentialGaussianMaximum
import BrownianSharp.AlignmentEndpointChainingBudget

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal
namespace BrownianSharp.AlignmentGaussianChainingRate
open AlignmentGaussianChaining AlignmentExponentialGaussianMaximum
open AlignmentEndpointChainingBudget

def chainingConstant (d : ℕ) : ℝ :=
  2*Real.sqrt ((d:ℝ)+2)+
    2*Real.sqrt (2*(d:ℝ)+2)*polynomialConstant+1

theorem chainingConstant_pos (d : ℕ) : 0<chainingConstant d := by
  unfold chainingConstant
  have h := polynomialConstant_pos
  positivity

/-- A quantitative continuum Gaussian chaining theorem. The input consists
only of point and increment Gaussian laws and variance bounds on actual
dyadic nearby pairs. No expected supremum premise is used. -/
theorem gaussian_chaining_expected_norm
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Ω→C(BrownianCubeAnchor d,ℝ))
    (hF : Measurable F) (v : BrownianCubeAnchor d→ℝ≥0)
    (vinc : (N : ℕ)→CubeNearPairs d N→ℝ≥0)
    (hLaw : ∀x,HasLaw (fun ω=>F ω x) (gaussianReal 0 (v x)) P)
    (hLawInc : ∀N (p : CubeNearPairs d N),HasLaw
      (fun ω=>F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (gaussianReal 0 (vinc N p)) P)
    (σ L : ℝ) (hσ : 0≤σ) (hL : 0≤L)
    (hvar : ∀x,(v x:ℝ)≤σ^2)
    (hvarInc : ∀N p,(vinc N p:ℝ)≤(L*(2:ℝ)^(-((N:ℝ)/2)))^2)
    (n₀ : ℕ) :
    Integrable (fun ω=>‖F ω‖) P ∧
      (∫ω,‖F ω‖ ∂P)≤chainingConstant d*Real.sqrt ((n₀:ℝ)+1)*
        (σ+L*(2:ℝ)^(-((n₀:ℝ)/2))) := by
  let U : ℝ := 2*Real.sqrt ((d:ℝ)+2)
  let V : ℝ := 2*Real.sqrt (2*(d:ℝ)+2)
  let B₀ : ℝ := U*σ*Real.sqrt ((n₀:ℝ)+1)
  let b : ℕ→ℝ := fun k=>V*L*((2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2))*
    Real.sqrt (((n₀+k:ℕ):ℝ)+2))
  have hU : 0≤U := by dsimp [U]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hb : ∀k,0≤b k := by intro k; dsimp [b]; positivity
  have hbs : Summable b := (summable_chaining_tail n₀).mul_left (V*L)
  have hbaseInt : Integrable (fun ω=>cubeGridMaximum n₀ (F ω)) P := by
    exact gaussian_max_abs_integrable
      (fun j : CubeDyadicGrid d n₀=>fun ω=>F ω (cubeDyadicAnchor j))
      (fun j=>hLaw _)
  have hincInt : ∀n,Integrable (fun ω=>cubeGridIncrementMaximum (n₀+n) (F ω)) P := by
    intro n
    exact gaussian_max_abs_integrable
      (fun p : CubeNearPairs d (n₀+n)=>fun ω=>
        F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (hLawInc (n₀+n))
  have hbase : (∫ω,cubeGridMaximum n₀ (F ω) ∂P)≤B₀ := by
    have hm := expected_max_le_sqrt_log
      (fun j : CubeDyadicGrid d n₀=>fun ω=>F ω (cubeDyadicAnchor j))
      (fun j=>hLaw _) hσ (fun j=>hvar _)
    calc
      _≤2*σ*Real.sqrt (Real.log (2*(Fintype.card (CubeDyadicGrid d n₀):ℝ)+2)) := hm
      _≤2*σ*Real.sqrt (((d:ℝ)+2)*((n₀:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (cubeGrid_log_card_le d n₀))
          (mul_nonneg (by norm_num) hσ)
      _=B₀ := by rw [Real.sqrt_mul (by positivity)]; dsimp [B₀,U]; ring
  have hinc : ∀n,(∫ω,cubeGridIncrementMaximum (n₀+n) (F ω) ∂P)≤b n := by
    intro n
    let N := n₀+n
    have hm := expected_max_le_sqrt_log
      (fun p : CubeNearPairs d N=>fun ω=>
        F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (hLawInc N) (show 0≤L*(2:ℝ)^(-((N:ℝ)/2)) by positivity) (hvarInc N)
    calc
      _≤2*(L*(2:ℝ)^(-((N:ℝ)/2)))*
          Real.sqrt (Real.log (2*(Fintype.card (CubeNearPairs d N):ℝ)+2)) := hm
      _≤2*(L*(2:ℝ)^(-((N:ℝ)/2)))*
          Real.sqrt ((2*(d:ℝ)+2)*((N:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (cubeNearPairs_log_card_le d N))
          (by positivity)
      _=b n := by rw [Real.sqrt_mul (by positivity)]; dsimp [b,V,N]; ring
  obtain ⟨hInt,hE⟩ := integrable_norm_and_integral_le_of_grid_bounds P F hF n₀
    B₀ (by dsimp [B₀]; positivity) b hb hbs hbaseInt hincInt hbase hinc
  refine ⟨hInt,hE.trans ?_⟩
  have hsum : (∑'k,b k)≤V*L*polynomialConstant*
      (2:ℝ)^(-((n₀:ℝ)/2))*Real.sqrt ((n₀:ℝ)+1) := by
    rw [show b=(fun k=>V*L*((2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2))*
      Real.sqrt (((n₀+k:ℕ):ℝ)+2))) by rfl,tsum_mul_left]
    have hh := mul_le_mul_of_nonneg_left (chaining_tail_le n₀) (mul_nonneg hV hL)
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using hh
  have hUC : U≤chainingConstant d := by
    dsimp [U,chainingConstant]
    have hc := mul_nonneg (Real.sqrt_nonneg (2*(d:ℝ)+2)) polynomialConstant_pos.le
    nlinarith
  have hVC : V*polynomialConstant≤chainingConstant d := by
    dsimp [V,chainingConstant]
    nlinarith [Real.sqrt_nonneg ((d:ℝ)+2)]
  calc
    B₀+∑'k,b k≤U*σ*Real.sqrt ((n₀:ℝ)+1)+
        V*L*polynomialConstant*(2:ℝ)^(-((n₀:ℝ)/2))*Real.sqrt ((n₀:ℝ)+1) :=
      add_le_add le_rfl hsum
    _≤chainingConstant d*σ*Real.sqrt ((n₀:ℝ)+1)+
        chainingConstant d*L*(2:ℝ)^(-((n₀:ℝ)/2))*Real.sqrt ((n₀:ℝ)+1) := by
      apply add_le_add
      · gcongr
      · calc
          _=(V*polynomialConstant)*L*(2:ℝ)^(-((n₀:ℝ)/2))*Real.sqrt ((n₀:ℝ)+1) := by ring
          _≤_ := by gcongr
    _=chainingConstant d*Real.sqrt ((n₀:ℝ)+1)*
        (σ+L*(2:ℝ)^(-((n₀:ℝ)/2))) := by ring

/-- Normalize the Gaussian chaining budget at the sharp hyperbolic Haar
variance scale. -/
theorem dyadic_chaining_budget_le {d : ℕ} (hd : 1≤d) (N : ℕ)
    (C L : ℝ) (hC : 0≤C) (hL : 0≤L) :
    chainingConstant d*Real.sqrt ((N:ℝ)+1)*
      (Real.sqrt (C*((2:ℝ)^N)⁻¹*((N:ℝ)+1)^(d-1))+
        L*(2:ℝ)^(-((N:ℝ)/2))) ≤
    (chainingConstant d*(Real.sqrt C+L))*(2:ℝ)^(-((N:ℝ)/2))*
      ((N:ℝ)+1)^((d:ℝ)/2) := by
  let s : ℝ := (N:ℝ)+1
  let p : ℝ := (2:ℝ)^(-((N:ℝ)/2))
  have hs : 0<s := by dsimp [s]; positivity
  have hs1 : 1≤s := by dsimp [s]; have h := Nat.cast_nonneg (α:=ℝ) N; linarith
  have hp : 0≤p := by dsimp [p]; positivity
  have hspow : s*s^(d-1)=s^d := by
    rw [←pow_succ',Nat.sub_add_cancel hd]
  have hroot : Real.sqrt s*Real.sqrt (C*((2:ℝ)^N)⁻¹*s^(d-1))=
      Real.sqrt C*p*Real.sqrt (s^d) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    have hp2 : p^2=((2:ℝ)^N)⁻¹ := dyadic_half_power_sq N
    simp only [mul_pow,Real.sq_sqrt hs.le,Real.sq_sqrt hC,
      Real.sq_sqrt (show 0≤C*((2:ℝ)^N)⁻¹*s^(d-1) by positivity),
      Real.sq_sqrt (show 0≤s^d by positivity),hp2]
    rw [←hspow]
    ring
  have hsqrtle : Real.sqrt s≤Real.sqrt (s^d) := by
    apply Real.sqrt_le_sqrt
    calc
      s=s^1 := by simp
      _≤s^d := pow_le_pow_right₀ hs1 hd
  have hsqrtpow : Real.sqrt (s^d)=s^((d:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hs.le]
    congr 1
    ring
  change chainingConstant d*Real.sqrt s*
    (Real.sqrt (C*((2:ℝ)^N)⁻¹*s^(d-1))+L*p)≤
    (chainingConstant d*(Real.sqrt C+L))*p*s^((d:ℝ)/2)
  calc
    _=chainingConstant d*(Real.sqrt C*p*Real.sqrt (s^d)+Real.sqrt s*L*p) := by
      rw [←hroot]
      ring
    _≤chainingConstant d*(Real.sqrt C*p*Real.sqrt (s^d)+Real.sqrt (s^d)*L*p) := by
      gcongr
      exact chainingConstant_pos d |>.le
    _=(chainingConstant d*(Real.sqrt C+L))*p*s^((d:ℝ)/2) := by
      rw [hsqrtpow]
      ring

end BrownianSharp.AlignmentGaussianChainingRate
