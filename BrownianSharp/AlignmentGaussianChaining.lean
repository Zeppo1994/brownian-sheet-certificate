import BrownianSharp.CubeDyadicGrid
import BrownianSharp.AlignmentAuditFatou
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace BrownianSharp.AlignmentGaussianChaining
open HaarQuarter

def cubeDyadicChoice {d : ℕ} (N : ℕ) (x : BrownianCubeAnchor d) :
    CubeDyadicGrid d N := Classical.choose (exists_cubeDyadicAnchor_near N x)

def cubeDyadicApprox {d : ℕ} (N : ℕ) (x : BrownianCubeAnchor d) :
    BrownianCubeAnchor d := cubeDyadicAnchor (cubeDyadicChoice N x)

theorem cubeDyadicApprox_dist_le {d : ℕ} (N : ℕ) (x : BrownianCubeAnchor d) :
    dist (cubeDyadicApprox N x) x≤((2:ℝ)^N)⁻¹ := by
  change dist (cubeDyadicApprox N x).val x.val≤_
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  have h := Classical.choose_spec (exists_cubeDyadicAnchor_near N x) i
  simpa only [cubeDyadicApprox,cubeDyadicChoice,Real.dist_eq,abs_sub_comm] using h.le

theorem cubeDyadicApprox_tendsto {d : ℕ} (x : BrownianCubeAnchor d) :
    Tendsto (fun N=>cubeDyadicApprox N x) atTop (𝓝 x) := by
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero (fun _=>dist_nonneg) (fun N=>cubeDyadicApprox_dist_le N x)
    (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)))

def CubeNearPairs (d N : ℕ) :=
  {p : CubeDyadicGrid d N × CubeDyadicGrid d (N+1) //
    dist (cubeDyadicAnchor p.1) (cubeDyadicAnchor p.2)≤2*((2:ℝ)^N)⁻¹}

instance (d N : ℕ) : Fintype (CubeNearPairs d N) := by
  classical
  unfold CubeNearPairs
  infer_instance

instance (d N : ℕ) : Nonempty (CubeNearPairs d N) := by
  refine ⟨⟨(0,0),?_⟩⟩
  have heq : cubeDyadicAnchor (0 : CubeDyadicGrid d N)=
      cubeDyadicAnchor (0 : CubeDyadicGrid d (N+1)) := by
    ext i
    simp [cubeDyadicAnchor]
  rw [heq,dist_self]
  positivity

def cubeApproxPair {d : ℕ} (N : ℕ) (x : BrownianCubeAnchor d) :
    CubeNearPairs d N :=
  ⟨(cubeDyadicChoice N x,cubeDyadicChoice (N+1) x),by
    change dist (cubeDyadicApprox N x) (cubeDyadicApprox (N+1) x)≤_
    have hinv : ((2:ℝ)^(N+1))⁻¹≤((2:ℝ)^N)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N))
    calc
      _≤dist (cubeDyadicApprox N x) x+dist x (cubeDyadicApprox (N+1) x) :=
        dist_triangle _ _ _
      _≤((2:ℝ)^N)⁻¹+((2:ℝ)^(N+1))⁻¹ := by
        exact add_le_add (cubeDyadicApprox_dist_le N x)
          (by simpa only [dist_comm] using cubeDyadicApprox_dist_le (N+1) x)
      _≤2*((2:ℝ)^N)⁻¹ := by linarith⟩

def cubeGridMaximum {d : ℕ} (N : ℕ) (f : C(BrownianCubeAnchor d,ℝ)) : ℝ :=
  ‖fun j : CubeDyadicGrid d N => f (cubeDyadicAnchor j)‖

def cubeGridIncrementMaximum {d : ℕ} (N : ℕ)
    (f : C(BrownianCubeAnchor d,ℝ)) : ℝ :=
  ‖fun p : CubeNearPairs d N =>
    f (cubeDyadicAnchor p.val.2)-f (cubeDyadicAnchor p.val.1)‖

theorem cubeGridMaximum_nonneg {d : ℕ} (N : ℕ) (f : C(BrownianCubeAnchor d,ℝ)) :
    0≤cubeGridMaximum N f := norm_nonneg _

theorem cubeGridIncrementMaximum_nonneg {d : ℕ} (N : ℕ)
    (f : C(BrownianCubeAnchor d,ℝ)) : 0≤cubeGridIncrementMaximum N f := norm_nonneg _

/-- The continuous path is bounded along its actual dyadic spatial chain,
using only maxima over finite sets of nearby grid pairs. -/
theorem cube_chain_pointwise_bound {d : ℕ} (n₀ n : ℕ)
    (f : C(BrownianCubeAnchor d,ℝ)) (x : BrownianCubeAnchor d) :
    |f (cubeDyadicApprox (n₀+n) x)|≤cubeGridMaximum n₀ f+
      ∑k∈Finset.range n,cubeGridIncrementMaximum (n₀+k) f := by
  induction n with
  | zero =>
    simpa only [Nat.add_zero,Finset.range_zero,Finset.sum_empty,add_zero,
      cubeDyadicApprox,cubeGridMaximum,Real.norm_eq_abs] using
      (norm_le_pi_norm (fun j : CubeDyadicGrid d n₀=>f (cubeDyadicAnchor j))
        (cubeDyadicChoice n₀ x))
  | succ n ih =>
    have hstep : |f (cubeDyadicApprox (n₀+n+1) x)-
        f (cubeDyadicApprox (n₀+n) x)|≤cubeGridIncrementMaximum (n₀+n) f := by
      simpa only [cubeGridIncrementMaximum,cubeApproxPair,cubeDyadicApprox,
        Real.norm_eq_abs] using
        (norm_le_pi_norm (fun p : CubeNearPairs d (n₀+n)=>
          f (cubeDyadicAnchor p.val.2)-f (cubeDyadicAnchor p.val.1))
          (cubeApproxPair (n₀+n) x))
    rw [Finset.sum_range_succ]
    have htri := abs_add_le (f (cubeDyadicApprox (n₀+n+1) x)-
      f (cubeDyadicApprox (n₀+n) x)) (f (cubeDyadicApprox (n₀+n) x))
    have heq : n₀+(n+1)=n₀+n+1 := by omega
    rw [heq]
    simp only [sub_add_cancel] at htri
    linarith

/-- Truncating the chain budget at the true supremum gives nonnegative
finite approximants converging to the full supremum, even before any
integrability or summability assumption is available. -/
theorem cube_chain_truncated_budget_tendsto {d : ℕ} (n₀ : ℕ)
    (f : C(BrownianCubeAnchor d,ℝ)) :
    Tendsto (fun n=>min ‖f‖ (cubeGridMaximum n₀ f+
      ∑k∈Finset.range n,cubeGridIncrementMaximum (n₀+k) f)) atTop (𝓝 ‖f‖) := by
  letI : Nonempty (BrownianCubeAnchor d) :=
    ⟨⟨0,fun _=>⟨by norm_num,by norm_num⟩⟩⟩
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.norm.continuousOn
  have hnorm : |f x|=‖f‖ := by
    apply le_antisymm (f.norm_coe_le_norm x)
    apply (ContinuousMap.norm_le _ (abs_nonneg _)).2
    intro y
    simpa only [Real.norm_eq_abs,Set.mem_setOf_eq] using hx (Set.mem_univ y)
  have hshift : Tendsto (fun n : ℕ=>n₀+n) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat n₀
  have hlimit := (f.continuous.tendsto x).comp
    ((cubeDyadicApprox_tendsto x).comp hshift)
  have habslimit : Tendsto (fun n=>|f (cubeDyadicApprox (n₀+n) x)|)
      atTop (𝓝 ‖f‖) := by simpa only [hnorm,Function.comp_apply] using hlimit.abs
  apply habslimit.squeeze tendsto_const_nhds
  · intro n
    exact le_min (f.norm_coe_le_norm _) (cube_chain_pointwise_bound n₀ n f x)
  · intro n
    exact min_le_left _ _

theorem cubeGridMaximum_continuous {d : ℕ} (N : ℕ) :
    Continuous (fun f : C(BrownianCubeAnchor d,ℝ)=>cubeGridMaximum N f) := by
  apply Continuous.norm
  apply continuous_pi
  intro j
  exact continuous_eval_const _

theorem cubeGridIncrementMaximum_continuous {d : ℕ} (N : ℕ) :
    Continuous (fun f : C(BrownianCubeAnchor d,ℝ)=>cubeGridIncrementMaximum N f) := by
  apply Continuous.norm
  apply continuous_pi
  intro p
  exact (continuous_eval_const _).sub (continuous_eval_const _)

theorem cubeNearPairs_card_le (d N : ℕ) :
    Fintype.card (CubeNearPairs d N)≤(2^N+1)^d*(2^(N+1)+1)^d := by
  calc
    _≤Fintype.card (CubeDyadicGrid d N × CubeDyadicGrid d (N+1)) :=
      Fintype.card_subtype_le _
    _=_ := by rw [Fintype.card_prod,cubeDyadicGrid_card,cubeDyadicGrid_card]

theorem cubeGridMaximum_le_norm {d : ℕ} (N : ℕ) (f : C(BrownianCubeAnchor d,ℝ)) :
    cubeGridMaximum N f≤‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro j
  exact f.norm_coe_le_norm _

theorem log_card_le_of_card_le_two_pow {ι : Type*} [Fintype ι]
    (a : ℕ) (hcard : Fintype.card ι≤2^a) :
    Real.log (2*(Fintype.card ι:ℝ)+2)≤(a:ℝ)+2 := by
  have hpow : (1:ℝ)≤2^a := one_le_pow₀ (by norm_num)
  have hc : (Fintype.card ι:ℝ)≤(2:ℝ)^a := by exact_mod_cast hcard
  have hle : 2*(Fintype.card ι:ℝ)+2≤4*(2:ℝ)^a := by linarith
  have hl2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hl4 : Real.log 4=2*Real.log 2 := by
    calc
      _=Real.log ((2:ℝ)^2) := by norm_num
      _=_ := by rw [Real.log_pow]; norm_num
  calc
    _≤Real.log (4*(2:ℝ)^a) := Real.log_le_log (by positivity) hle
    _=2*Real.log 2+(a:ℝ)*Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
      rw [hl4]
    _≤(a:ℝ)+2 := by nlinarith

theorem cubeGrid_log_card_le (d N : ℕ) :
    Real.log (2*(Fintype.card (CubeDyadicGrid d N):ℝ)+2)≤
      ((d:ℝ)+2)*((N:ℝ)+1) := by
  have hbase : 2^N+1≤2^(N+1) := by
    have h := Nat.one_le_pow N 2 (by omega)
    rw [Nat.pow_succ]
    omega
  have hc : Fintype.card (CubeDyadicGrid d N)≤2^((N+1)*d) := by
    rw [cubeDyadicGrid_card,Nat.pow_mul]
    exact Nat.pow_le_pow_left hbase d
  have h := log_card_le_of_card_le_two_pow ((N+1)*d) hc
  push_cast at h
  nlinarith [h]

theorem cubeNearPairs_log_card_le (d N : ℕ) :
    Real.log (2*(Fintype.card (CubeNearPairs d N):ℝ)+2)≤
      (2*(d:ℝ)+2)*((N:ℝ)+2) := by
  have hbase₁ : 2^N+1≤2^(N+1) := by
    have h := Nat.one_le_pow N 2 (by omega)
    rw [Nat.pow_succ]
    omega
  have hbase₂ : 2^(N+1)+1≤2^(N+2) := by
    have h := Nat.one_le_pow (N+1) 2 (by omega)
    rw [show N+2=(N+1)+1 by omega,Nat.pow_succ]
    omega
  have hc : Fintype.card (CubeNearPairs d N)≤2^((N+1)*d+(N+2)*d) := by
    calc
      _≤(2^N+1)^d*(2^(N+1)+1)^d := cubeNearPairs_card_le d N
      _≤(2^(N+1))^d*(2^(N+2))^d :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hbase₁ d) (Nat.pow_le_pow_left hbase₂ d)
      _=_ := by rw [←Nat.pow_mul,←Nat.pow_mul,←Nat.pow_add]
  have h := log_card_le_of_card_le_two_pow ((N+1)*d+(N+2)*d) hc
  push_cast at h
  nlinarith [h]

/-- Finite expected grid maxima control the expected norm of the actual
continuous path. Integrability of the supremum is a conclusion. -/
theorem integrable_norm_and_integral_le_of_grid_bounds
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω→C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
    (n₀ : ℕ) (B₀ : ℝ) (hB₀ : 0≤B₀) (b : ℕ→ℝ)
    (hb : ∀n,0≤b n) (hbs : Summable b)
    (hbaseInt : Integrable (fun ω=>cubeGridMaximum n₀ (F ω)) P)
    (hincInt : ∀n,Integrable (fun ω=>cubeGridIncrementMaximum (n₀+n) (F ω)) P)
    (hbase : (∫ω,cubeGridMaximum n₀ (F ω) ∂P)≤B₀)
    (hinc : ∀n,(∫ω,cubeGridIncrementMaximum (n₀+n) (F ω) ∂P)≤b n) :
    Integrable (fun ω=>‖F ω‖) P ∧
      (∫ω,‖F ω‖ ∂P)≤B₀+∑'n,b n := by
  let budget : ℕ→Ω→ℝ := fun n ω=>cubeGridMaximum n₀ (F ω)+
    ∑k∈Finset.range n,cubeGridIncrementMaximum (n₀+k) (F ω)
  let trunc : ℕ→Ω→ℝ := fun n ω=>min ‖F ω‖ (budget n ω)
  have hbudgetInt : ∀n,Integrable (budget n) P := by
    intro n
    exact hbaseInt.add (integrable_finsetSum _ (fun k _=>hincInt k))
  have hbudgetMeas : ∀n,Measurable (budget n) := by
    intro n
    exact ((cubeGridMaximum_continuous n₀).measurable.comp hF).add
      (Finset.measurable_sum _ (fun k _=>
        (cubeGridIncrementMaximum_continuous (n₀+k)).measurable.comp hF))
  have hbudget0 : ∀n ω,0≤budget n ω := by
    intro n ω
    exact add_nonneg (cubeGridMaximum_nonneg _ _)
      (Finset.sum_nonneg (fun _ _=>cubeGridIncrementMaximum_nonneg _ _))
  have htruncMeas : ∀n,Measurable (trunc n) := by
    intro n
    exact hF.norm.min (hbudgetMeas n)
  have htrunc0 : ∀n ω,0≤trunc n ω := by
    intro n ω
    exact le_min (norm_nonneg _) (hbudget0 n ω)
  have htruncInt : ∀n,Integrable (trunc n) P := by
    intro n
    apply (hbudgetInt n).mono' (htruncMeas n).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg (htrunc0 n ω)] using
      (min_le_right ‖F ω‖ (budget n ω))
  have htruncBound : ∀n,(∫ω,trunc n ω ∂P)≤B₀+∑'k,b k := by
    intro n
    calc
      _≤∫ω,budget n ω ∂P := integral_mono (htruncInt n) (hbudgetInt n)
        (fun ω=>min_le_right _ _)
      _=(∫ω,cubeGridMaximum n₀ (F ω) ∂P)+
          ∑k∈Finset.range n,∫ω,cubeGridIncrementMaximum (n₀+k) (F ω) ∂P := by
        change (∫ω,cubeGridMaximum n₀ (F ω)+
          ∑k∈Finset.range n,cubeGridIncrementMaximum (n₀+k) (F ω) ∂P)=_
        rw [integral_add hbaseInt (integrable_finsetSum _ (fun k _=>hincInt k)),
          integral_finset_sum _ (fun k _=>hincInt k)]
      _≤B₀+∑k∈Finset.range n,b k :=
        add_le_add hbase (Finset.sum_le_sum (fun k _=>hinc k))
      _≤B₀+∑'k,b k := add_le_add le_rfl (hbs.sum_le_tsum _ (fun k _=>hb k))
  exact AlignmentAuditFatou.integrable_limit_and_integral_le_of_nonneg_tendsto
    P trunc (fun ω=>‖F ω‖) (B₀+∑'k,b k)
    (add_nonneg hB₀ (tsum_nonneg hb)) htruncInt htruncMeas hF.norm
    htrunc0 htruncBound (Filter.Eventually.of_forall (fun ω=>
      cube_chain_truncated_budget_tendsto n₀ (F ω)))

theorem dyadic_half_power_sq (N : ℕ) :
    ((2:ℝ)^(-((N:ℝ)/2)))^2=((2:ℝ)^N)⁻¹ := by
  calc
    _=(2:ℝ)^((-((N:ℝ)/2))*2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      norm_num
    _=(2:ℝ)^(-(N:ℝ)) := by congr 1; ring
    _=((2:ℝ)^N)⁻¹ := by rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]

/-- A canonical-metric Lipschitz variance bound gives the exact increment
variance input used by the dyadic chaining theorem. -/
theorem nearPair_variance_bound {d N : ℕ} (R : ℝ) (hR : 0≤R)
    (v : BrownianCubeAnchor d→BrownianCubeAnchor d→ℝ)
    (hv : ∀x y,v x y≤R*dist x y) (p : CubeNearPairs d N) :
    v (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1)≤
      (Real.sqrt (2*R)*(2:ℝ)^(-((N:ℝ)/2)))^2 := by
  calc
    _≤R*dist (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1) := hv _ _
    _≤R*(2*((2:ℝ)^N)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hR
      simpa only [dist_comm] using p.property
    _=(Real.sqrt (2*R)*(2:ℝ)^(-((N:ℝ)/2)))^2 := by
      rw [mul_pow,Real.sq_sqrt (by positivity),dyadic_half_power_sq]
      ring

end BrownianSharp.AlignmentGaussianChaining
