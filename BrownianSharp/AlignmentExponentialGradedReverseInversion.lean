import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace BrownianSharp.AlignmentExponentialGradedReverseInversion

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

def radiusProfile (β : ℝ) (d : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  A * (2 : ℝ) ^ (-β * (N : ℝ) / 2) * ((N + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2)

/-- Choose a dyadic radius below ε while keeping the rate cost at the sharp
ε⁻²(log ε⁻¹)^(2d−1) scale. -/
theorem exists_dyadic_radius_index (d N₀ : ℕ) (hd : 2 ≤ d)
    {A β : ℝ} (hA : 0 < A) (hβ : 0 < β) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ N : ℕ, N₀ ≤ N ∧ radiusProfile β d A N ≤ ε ∧
          (2 : ℝ) ^ N * ((N + 1 : ℕ) : ℝ) ^ (d - 1) ≤
            C * Real.rpow ε⁻¹ (2/β) *
              Real.rpow (Real.log ε⁻¹) ((d:ℝ)-1+(d:ℝ)/β) := by
  let a : ℝ := (d : ℝ) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1/2 : ℝ) ≤ Real.log 2 := by
    have haux := Real.le_log_one_add_of_nonneg (x := (1:ℝ)) (by norm_num)
    norm_num at haux ⊢
    linarith
  have hβlog2 : 0 < β * Real.log 2 := mul_pos hβ hlog2pos
  let Q : ℝ := ((d : ℝ) + 2) / (β * Real.log 2) + 3
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQlarge : 1 ≤ Q := by
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    dsimp [Q]
    have hquot : 0 ≤ ((d:ℝ)+2) / (β*Real.log 2) := by positivity
    have hquot' : 1 ≤ ((d:ℝ)+2) / (β*Real.log 2) + 3 := by linarith
    exact hquot'
  let R : ℝ := A * Q ^ a
  have hR : 0 < R := mul_pos hA (Real.rpow_pos_of_pos hQ _)
  let J0 : ℕ := Nat.ceil (max 0 ((2 / (β*Real.log 2)) * Real.log R))
  let J : ℕ := max N₀ (J0 + 1)
  have hJ0 : 0 ≤ max 0 ((2 / (β*Real.log 2)) * Real.log R) := le_max_left _ _
  have hJscale : (2 / (β*Real.log 2)) * Real.log R ≤ (J : ℝ) := by
    have hceil : max 0 ((2 / (β*Real.log 2)) * Real.log R) ≤ (J0 : ℝ) := by
      dsimp [J0]
      exact Nat.le_ceil _
    have hJ0le : J0 ≤ J := by dsimp [J]; omega
    have hmax : (2 / (β*Real.log 2)) * Real.log R ≤ max 0 ((2 / (β*Real.log 2)) * Real.log R) := le_max_right _ _
    exact hmax.trans (hceil.trans (by exact_mod_cast hJ0le))
  have hJnat : N₀ ≤ J := by dsimp [J]; exact le_max_left _ _
  have hJpos : 0 < J := by
    have : 1 ≤ J := by dsimp [J]; omega
    omega
  let ε₀ : ℝ := Real.exp (-(J : ℝ))
  have hε₀ : 0 < ε₀ := Real.exp_pos _
  have hC : 0 < (2 : ℝ) ^ (J + 1) * Q ^ (d - 1) := by positivity
  refine ⟨ε₀, (2 : ℝ) ^ (J + 1) * Q ^ (d - 1), hε₀, hC, ?_⟩
  intro ε hε hεsmall
  let L : ℝ := Real.log ε⁻¹
  have hL : (J : ℝ) ≤ L := by
    have hε' : ε ≤ Real.exp (-(J : ℝ)) := by simpa [ε₀] using hεsmall
    have hlogε : Real.log ε ≤ -(J : ℝ) := by
      calc Real.log ε ≤ Real.log (Real.exp (-(J : ℝ))) := Real.log_le_log hε hε'
        _ = -(J : ℝ) := Real.log_exp _
    dsimp [L]
    rw [Real.log_inv]
    linarith
  have hL1 : 1 ≤ L := by
    have hJ1 : (1:ℝ) ≤ (J:ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hJpos)
    exact hJ1.trans hL
  have hLpos : 0 < L := by linarith
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  let x : ℝ := (2 / (β*Real.log 2)) * L + ((d : ℝ) / (β*Real.log 2)) * Real.log L
  let N : ℕ := Nat.ceil x + J
  have hxpos : 0 ≤ x := by
    dsimp [x]
    have hlogLnonneg : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    positivity
  have hxceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil _
  have hNlower : (x + (J:ℝ)) ≤ (N:ℝ) := by
    dsimp [N]
    rw [Nat.cast_add]
    linarith
  have hNlowerN0 : N₀ ≤ N := by
    have hJle : (N₀:ℝ) ≤ (N:ℝ) := by
      have hJle' : (N₀:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJnat
      linarith
    exact_mod_cast hJle
  have hceilhi : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos
  have hxupper : x ≤ ((d:ℝ)+2) / (β*Real.log 2) * L := by
    have hnum : 2*L + (d:ℝ)*Real.log L ≤ ((d:ℝ)+2)*L := by nlinarith [hlogL]
    have hdiv := div_le_div_of_nonneg_right hnum hβlog2.le
    calc
      x = (2*L + (d:ℝ)*Real.log L) / (β*Real.log 2) := by dsimp [x]; field_simp
      _ ≤ ((d:ℝ)+2)*L / (β*Real.log 2) := hdiv
      _ = ((d:ℝ)+2) / (β*Real.log 2) * L := by ring
  have hQbound : ((N + 1 : ℕ) : ℝ) ≤ Q * L := by
    have hNexpr : (N:ℝ) < x + 1 + (J:ℝ) := by
      dsimp [N]
      rw [Nat.cast_add]
      linarith
    have hJleL : (J:ℝ) ≤ L := hL
    have hL1 : 1 ≤ L := hL1
    have hQeq : Q = ((d:ℝ)+2) / (β*Real.log 2) + 3 := rfl
    rw [Nat.cast_add, Nat.cast_one, hQeq]
    have hfirst : (N:ℝ)+1 ≤ x + (J:ℝ) + 2 := by linarith
    have hsecond : x + (J:ℝ) + 2 ≤ ((d:ℝ)+2) / (β*Real.log 2) * L + L + 2 := by
      calc
        x + (J:ℝ) + 2 = (x+2) + (J:ℝ) := by ring
        _ ≤ ((d:ℝ)+2) / (β*Real.log 2) * L + 2 + L := by
          have h1 : x + 2 ≤ ((d:ℝ)+2) / (β*Real.log 2) * L + 2 := by
            simpa [add_comm] using add_le_add_right hxupper 2
          have h2 := add_le_add h1 hJleL
          nlinarith [h2]
        _ = _ := by ring
    have hthird : ((d:ℝ)+2) / (β*Real.log 2) * L + L + 2 ≤
        (((d:ℝ)+2) / (β*Real.log 2) + 3) * L := by nlinarith [hL1]
    exact hfirst.trans (hsecond.trans hthird)
  have hxidentity : x * (β*Real.log 2) / 2 = L + a * Real.log L := by
    dsimp [x,a]
    field_simp
  have hNlowerexp : L + a * Real.log L + β*(J:ℝ) * Real.log 2 / 2 ≤
      β*(N:ℝ) * Real.log 2 / 2 := by
    calc
      L + a * Real.log L + β*(J:ℝ) * Real.log 2 / 2 =
          (x + (J:ℝ)) * (β*Real.log 2) / 2 := by rw [← hxidentity]; ring
      _ ≤ β*(N:ℝ) * Real.log 2 / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hNlower (by positivity : 0 ≤ β*Real.log 2 / 2)
        nlinarith [hmul]
  have hlogR' : Real.log R = Real.log A + a * Real.log Q := by
    dsimp [R]
    rw [Real.log_mul hA.ne' (ne_of_gt (Real.rpow_pos_of_pos hQ _)), Real.log_rpow hQ]
  have hRscale : Real.log R ≤ β*(J:ℝ) * Real.log 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hJscale (by positivity : 0 ≤ β*Real.log 2 / 2)
    have heq : ((2 / (β*Real.log 2)) * Real.log R) * (β*Real.log 2) / 2 = Real.log R := by field_simp
    calc
      Real.log R = ((2 / (β*Real.log 2)) * Real.log R) * (β*Real.log 2) / 2 := heq.symm
      _ ≤ β*(J:ℝ) * Real.log 2 / 2 := by nlinarith [hmul]
  have hbaseexp : (2:ℝ) ^ (-β*(N:ℝ)/2) =
      Real.exp (-β*(N:ℝ) * Real.log 2 / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2) (-β*(N:ℝ)/2)]
    congr 1
    ring_nf
  have hpowL : (L:ℝ)^a = Real.exp (a * Real.log L) := by
    rw [Real.rpow_def_of_pos hLpos, mul_comm]
  have hpowNL : (((N+1:ℕ):ℝ))^a ≤ (Q*L)^a :=
    Real.rpow_le_rpow (by positivity) hQbound (by positivity)
  have hrad : radiusProfile β d A N ≤ ε := by
    dsimp [radiusProfile]
    rw [show (d:ℝ)/2 = a by rfl, hbaseexp]
    have hpowQL : (Q*L)^a = Real.exp (a*Real.log Q + a*Real.log L) := by
      rw [Real.mul_rpow hQ.le hLpos.le, Real.rpow_def_of_pos hQ,
        Real.rpow_def_of_pos hLpos, Real.exp_add]
      congr 1 <;> ring
    have hineq : Real.log A - β*(N:ℝ)*Real.log 2/2 + a*Real.log Q + a*Real.log L ≤ -L := by
      have hbase := neg_le_neg hNlowerexp
      nlinarith [hbase, hRscale, hlogR']
    have hexp : A * Real.exp (-β*(N:ℝ)*Real.log 2/2) * (Q*L)^a ≤ Real.exp (-L) := by
      rw [hpowQL]
      have hAexp : A = Real.exp (Real.log A) := (Real.exp_log hA).symm
      have heq : A * Real.exp (-β*(N:ℝ)*Real.log 2/2) *
          Real.exp (a*Real.log Q + a*Real.log L) =
          Real.exp (Real.log A - β*(N:ℝ)*Real.log 2/2 + a*Real.log Q + a*Real.log L) := by
        calc
          _ = Real.exp (Real.log A) * Real.exp (-β*(N:ℝ)*Real.log 2/2) *
              Real.exp (a*Real.log Q + a*Real.log L) := by
                conv_lhs => rw [hAexp]
          _ = Real.exp (Real.log A - β*(N:ℝ)*Real.log 2/2 + a*Real.log Q + a*Real.log L) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
      rw [heq]
      exact Real.exp_le_exp.mpr hineq
    have hRinv : Real.exp (-L) = ε := by
      simp [L, Real.log_inv, Real.exp_log hε]
    calc
      A * Real.exp (-β*(N:ℝ)*Real.log 2/2) * ((N+1:ℕ):ℝ)^a ≤
          A * Real.exp (-β*(N:ℝ)*Real.log 2/2) * (Q*L)^a := by gcongr
      _ ≤ ε := by
        rw [← hRinv]
        exact hexp
  have hcost : (2:ℝ)^N * ((N+1:ℕ):ℝ)^(d-1) ≤
      ((2:ℝ)^(J+1) * Q^(d-1)) * Real.rpow ε⁻¹ (2/β) *
        Real.rpow L ((d:ℝ)-1+(d:ℝ)/β) := by
    have hNupperExp : (N:ℝ)*Real.log 2 ≤
        (2/β)*L + ((d:ℝ)/β)*Real.log L + ((J:ℝ)+1)*Real.log 2 := by
      have hNexpr : (N:ℝ) < x + 1 + (J:ℝ) := by
        dsimp [N]
        rw [Nat.cast_add]
        linarith
      dsimp [x] at hNexpr
      have hmul := mul_le_mul_of_nonneg_right hNexpr.le hlog2pos.le
      have hxlog : x * Real.log 2 = (2/β)*L + ((d:ℝ)/β)*Real.log L := by
        dsimp [x]
        field_simp
      nlinarith [hmul, hxlog]

    have hpowN : (2:ℝ)^N ≤ (2:ℝ)^(J+1) * Real.rpow ε⁻¹ (2/β) *
        Real.rpow L ((d:ℝ)/β) := by
      have hpow : (2:ℝ)^N = Real.exp ((N:ℝ)*Real.log 2) := by
        calc (2:ℝ)^N = (2:ℝ)^(N:ℝ) := by rw [← Real.rpow_natCast]
          _ = Real.exp (Real.log 2 * (N:ℝ)) := Real.rpow_def_of_pos (by norm_num) (N:ℝ)
          _ = _ := by rw [mul_comm]
      have hLpow : Real.rpow L ((d:ℝ)/β) =
          Real.exp (((d:ℝ)/β)*Real.log L) := by
        calc
          Real.rpow L ((d:ℝ)/β) = Real.exp (Real.log L * ((d:ℝ)/β)) :=
            Real.rpow_def_of_pos hLpos _
          _ = Real.exp (((d:ℝ)/β)*Real.log L) := by congr 1; ring
      have heps : Real.exp ((2/β)*L) = Real.rpow ε⁻¹ (2/β) := by
        calc
          Real.exp ((2/β)*L) = Real.exp (Real.log (ε⁻¹) * (2/β)) := by
            dsimp [L]
            congr 1; ring
          _ = Real.rpow ε⁻¹ (2/β) := by
            symm
            exact Real.rpow_def_of_pos (by positivity : 0<ε⁻¹) _
      rw [hpow, hLpow]
      calc
        Real.exp ((N:ℝ)*Real.log 2) ≤
            Real.exp ((2/β)*L + ((d:ℝ)/β)*Real.log L + ((J:ℝ)+1)*Real.log 2) :=
          Real.exp_le_exp.mpr hNupperExp
        _ = (2:ℝ)^(J+1) * Real.rpow ε⁻¹ (2/β) *
            Real.exp (((d:ℝ)/β)*Real.log L) := by
          rw [Real.exp_add, Real.exp_add]
          have hJexp : Real.exp (((J:ℝ)+1)*Real.log 2) = (2:ℝ)^(J+1) := by
            calc
              Real.exp (((J:ℝ)+1)*Real.log 2) = (2:ℝ)^((J+1:ℕ):ℝ) := by
                rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
                congr 1
                push_cast
                ring
              _ = (2:ℝ)^(J+1) := by rw [Real.rpow_natCast]
          rw [hJexp, heps]
          ring
    have hpowGrade : ((N+1:ℕ):ℝ)^(d-1) ≤ (Q*L)^(d-1) := by
      exact pow_le_pow_left₀ (by positivity) hQbound _
    calc
      (2:ℝ)^N * ((N+1:ℕ):ℝ)^(d-1) ≤
          ((2:ℝ)^(J+1) * Real.rpow ε⁻¹ (2/β) * Real.rpow L ((d:ℝ)/β)) * (Q*L)^(d-1) :=
        mul_le_mul hpowN hpowGrade (by positivity : 0≤((N+1:ℕ):ℝ)^(d-1))
          (mul_nonneg (mul_nonneg (by positivity)
            (le_of_lt (Real.rpow_pos_of_pos (by positivity) _)))
            (le_of_lt (Real.rpow_pos_of_pos hLpos _)))
      _ = ((2:ℝ)^(J+1) * Real.rpow ε⁻¹ (2/β) * Q^(d-1)) *
          (Real.rpow L ((d:ℝ)/β) * Real.rpow L ((d:ℝ)-1)) := by
        rw [mul_pow]
        have hnat : L^(d-1)=Real.rpow L ((d:ℝ)-1) := by
          have hcast : ((d-1:ℕ):ℝ)=(d:ℝ)-1 := by exact_mod_cast Nat.cast_sub (by omega : 1≤d)
          calc
            L^(d-1) = Real.rpow L ((d-1:ℕ):ℝ) := (Real.rpow_natCast L (d-1)).symm
            _ = Real.rpow L ((d:ℝ)-1) := by rw [hcast]
        rw [hnat]
        ring
      _ = ((2:ℝ)^(J+1)*Q^(d-1))*Real.rpow ε⁻¹ (2/β) *
          Real.rpow L ((d:ℝ)-1+(d:ℝ)/β) := by
        calc
          _ = ((2:ℝ)^(J+1)*Q^(d-1))*Real.rpow ε⁻¹ (2/β) *
              (Real.rpow L ((d:ℝ)-1) * Real.rpow L ((d:ℝ)/β)) := by ring
          _ = _ := by
            have hp := (Real.rpow_add hLpos ((d:ℝ)-1) ((d:ℝ)/β)).symm
            exact congrArg
              (fun z : ℝ => ((2:ℝ)^(J+1)*Q^(d-1)*Real.rpow ε⁻¹ (2/β))*z) hp
  refine ⟨N,hNlowerN0,hrad,?_⟩
  simpa [L] using hcost

end
end BrownianSharp.AlignmentExponentialGradedReverseInversion
