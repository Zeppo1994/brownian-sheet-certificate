import BrownianSharp.PeriodicEntropy
import BrownianSharp.LayerIndex
import BrownianSharp.ShapeGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

noncomputable section
open Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

namespace BrownianSharp.AlignmentTensorApproximationUpperRate

open BrownianSharp

private theorem crossing_grade_eventually_ge {d N : ℕ} (hd : 2 ≤ d) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      N ≤ 2 * nativeEntropyCrossing d m (by omega) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let L := nativeLogScaleLower d
  have hL : 0 < L := nativeLogScaleLower_pos hd
  have hev : ∀ᶠ m : ℕ in atTop,
      N ≤ 2 * nativeEntropyCrossing d m (by omega) := by
    filter_upwards [hlog.eventually_ge_atTop (L*(N:ℝ)), eventually_ge_atTop 2]
      with m hlarge hm
    have hcross := (nativeEntropyCrossing_log_bounds hd hm).1
    have hq : (N:ℝ) ≤ (nativeEntropyCrossing d m (by omega):ℝ) := by
      have hlarge' : L*(N:ℝ) ≤ Real.log (m:ℝ) := by simpa [L] using hlarge
      have hcross' : Real.log (m:ℝ) ≤ L*(nativeEntropyCrossing d m (by omega):ℝ) := by
        simpa [L,nativeLogScaleLower] using hcross
      nlinarith [hL]
    exact_mod_cast (show (N:ℝ) ≤ 2*(nativeEntropyCrossing d m (by omega):ℝ) by nlinarith)
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.1 hev
  exact ⟨max 2 m₀, le_max_left _ _, fun m hm =>
    hm₀ m ((le_max_right _ _).trans hm)⟩

/-- Eventual all-index upper transfer from an upper bound on one tensor layer.
The layer index may include any fixed positive integer rank factor. -/
theorem all_index_upper_of_layer_bound
    {d : ℕ} (hd : 2 ≤ d) (β A : ℝ) (hβ : 0 < β) (hA : 0 < A)
    (R N₀ : ℕ) (hR : 0 < R) (f : ℕ → ℝ≥0∞)
    (hfmono : ∀ ⦃i j : ℕ⦄, i ≤ j → f j ≤ f i)
    (hlayer : ∀ N : ℕ, N₀ ≤ N →
      f (R * Fintype.card (LayerIndex d N) + 1) ≤
        ENNReal.ofReal (A * (2:ℝ)^(-β*(N:ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        f k ≤ ENNReal.ofReal (C * (k:ℝ)^(-β) *
          (Real.log (k:ℝ))^(β*((d-1:ℕ):ℝ))) := by
  classical
  let F : ℝ := ((d-1:ℕ):ℝ)
  let Q := nativeLogScaleUpper d
  let L := 2*Q+1
  let U := 16*(R:ℝ)*(d:ℝ)^2*L^F
  let C := A*U^β
  obtain ⟨m₀,hm₀,hmgrade⟩ := crossing_grade_eventually_ge (d:=d) (N:=N₀+2) hd
  let k₀ := max (4*R) (2*R*m₀)
  refine ⟨C, ?_, max k₀ 2, le_max_right _ _, ?_⟩
  · dsimp [C,U,L,Q]
    have hQ : 0 < nativeLogScaleUpper d := nativeLogScaleUpper_pos hd
    have hL : 0 < 2*nativeLogScaleUpper d+1 := by positivity
    have hR' : 0 < (R:ℝ) := by exact_mod_cast hR
    have hd' : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0<d)
    have hU : 0 < 16*(R:ℝ)*(d:ℝ)^2*(2*nativeLogScaleUpper d+1)^F := by positivity
    exact mul_pos hA (Real.rpow_pos_of_pos hU β)
  · intro k hk
    have hk' : max (4*R) (2*R*m₀) ≤ k := by
      simpa [k₀] using (le_trans (le_max_left k₀ 2) hk)
    have hk2 : 2 ≤ k := (le_max_right _ _).trans hk
    have hkR : 4*R ≤ k := (le_max_left _ _).trans hk'
    have hkm₀ : 2*R*m₀ ≤ k := (le_max_right _ _).trans hk'
    let m : ℕ := k/(2*R)
    have hmpos : 2 ≤ m := by
      have hdiv : 2*(2*R) ≤ k := by omega
      dsimp [m]
      exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_comm] using hdiv)
    have hqbound : N₀+2 ≤ 2*nativeEntropyCrossing d m (by omega) := by
      have hdiv : m₀ ≤ m := by
        dsimp [m]
        exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_comm] using hkm₀)
      exact hmgrade m hdiv
    let q := nativeEntropyCrossing d m (by omega)
    let N := 2*(q-1)
    let D := Fintype.card (LayerIndex d N)
    have hbr := nativeEntropyCrossing_bracket hd hmpos
    have hqpos : 0<q := by dsimp [q]; exact hbr.1
    have hN0 : N₀ ≤ N := by dsimp [N]; omega
    have hprev : nativeDimension d N < (m:ℝ) := by
      simpa [N,q] using hbr.2.1
    have hcurr : (m:ℝ) ≤ nativeDimension d (N+2) := by
      have hq1 : 1≤q := hqpos
      have hN2 : N+2=2*q := by dsimp [N]; omega
      rw [hN2]
      exact hbr.2.2.1
    have hstep1 := nativeDimension_step_le (d:=d) (n:=N) (by omega)
    have hstep2 := nativeDimension_step_le (d:=d) (n:=N+1) (by omega)
    have hdimstep : nativeDimension d (N+2) ≤
        (4*(d:ℝ)^2)*nativeDimension d N := by
      calc
        nativeDimension d (N+2) ≤ (2*(d:ℝ))*nativeDimension d (N+1) := by
          simpa [Nat.add_assoc] using hstep2
        _ ≤ (2*(d:ℝ))*((2*(d:ℝ))*nativeDimension d N) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = (4*(d:ℝ)^2)*nativeDimension d N := by ring
    have hDlower : (m:ℝ)/(4*(d:ℝ)^2) ≤ nativeDimension d N := by
      have hdpos : 0<(4:ℝ)*(d:ℝ)^2 := by positivity
      apply (div_le_iff₀ hdpos).2
      calc
        (m:ℝ) ≤ nativeDimension d (N+2) := hcurr
        _ ≤ (4*(d:ℝ)^2)*nativeDimension d N := hdimstep
        _ = nativeDimension d N*(4*(d:ℝ)^2) := by ring
    have hDident : (D:ℝ)=nativeDimension d N := by
      change (Fintype.card (LayerIndex d N):ℝ)=nativeDimension d N
      rw [layerIndex_card d N (by omega : 0<d)]
      simp [nativeDimension,hyperbolicCount]
    have hDpos : 0<(D:ℝ) := by
      have hmR : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
      have hconst : 0<(4:ℝ)*(d:ℝ)^2 := by positivity
      rw [hDident]
      exact (div_pos hmR hconst).trans_le hDlower
    have hindex : R*D+1 ≤ k := by
      have hprevNat : D < m := by
        have : (D:ℝ)<(m:ℝ) := by rw [hDident]; exact hprev
        exact_mod_cast this
      have hAm : R*m ≤ k := by
        calc
          R*m ≤ (2*R)*m := Nat.mul_le_mul_right m (by omega)
          _ = m*(2*R) := by ring
          _ ≤ k := by dsimp [m]; exact Nat.div_mul_le_self k (2*R)
      have hRD : R*D < R*m := Nat.mul_lt_mul_of_pos_left hprevNat hR
      exact (Nat.succ_le_of_lt hRD).trans hAm
    have hfreq : hyperbolicCount d N ≤ ((N:ℝ)+1)^F := by
      simpa [F, Real.rpow_natCast] using
        (hyperbolicCount_upper_shift (d:=d) (by omega : 1≤d) N)
    have hDformula : nativeDimension d N=(2:ℝ)^N*hyperbolicCount d N := rfl
    have hdyadic : (2:ℝ)^(-(N:ℝ)) ≤
        (4*(d:ℝ)^2)*((N:ℝ)+1)^F/(m:ℝ) := by
      have hNpos : 0 < (2:ℝ)^N := by positivity
      have h2lower : (m:ℝ) ≤
          (4*(d:ℝ)^2)*(D:ℝ) := by
        have h := hDlower
        have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0≤(4:ℝ)*(d:ℝ)^2)
        nlinarith
      have hquotient : (D:ℝ) ≤ (2:ℝ)^N*((N:ℝ)+1)^F := by
        rw [hDident,hDformula]
        exact mul_le_mul_of_nonneg_left hfreq (by positivity)
      have hkey : (2:ℝ)^N ≥ (m:ℝ)/((4*(d:ℝ)^2)*((N:ℝ)+1)^F) := by
        have hmD : (m:ℝ)/((4*(d:ℝ)^2)) ≤ (D:ℝ) := by
          rw [hDident]
          exact hDlower
        have hdenpos : 0<(4:ℝ)*(d:ℝ)^2 := by positivity
        have hcombine : (m:ℝ)/((4*(d:ℝ)^2)*((N:ℝ)+1)^F) ≤
            (D:ℝ)/((N:ℝ)+1)^F := by
          calc
            (m:ℝ)/((4*(d:ℝ)^2)*((N:ℝ)+1)^F) =
                ((m:ℝ)/(4*(d:ℝ)^2))/((N:ℝ)+1)^F := by field_simp
            _ ≤ (D:ℝ)/((N:ℝ)+1)^F :=
              div_le_div_of_nonneg_right hmD (by positivity)
        have hcombine2 : (D:ℝ)/((N:ℝ)+1)^F ≤ (2:ℝ)^N := by
          apply (div_le_iff₀ (by positivity)).2
          simpa [mul_comm] using hquotient
        exact hcombine.trans hcombine2
      have hrecip : ((2:ℝ)^N)⁻¹ ≤
          ((4*(d:ℝ)^2)*((N:ℝ)+1)^F)/(m:ℝ) := by
        calc
          ((2:ℝ)^N)⁻¹ ≤ ((m:ℝ)/((4*(d:ℝ)^2)*((N:ℝ)+1)^F))⁻¹ :=
            (inv_le_inv₀ (by positivity) (by positivity)).2 hkey
          _ = ((4*(d:ℝ)^2)*((N:ℝ)+1)^F)/(m:ℝ) := by
            field_simp
      simpa [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast] using hrecip
    have hlogm : Real.log (m:ℝ) ≤ Real.log (k:ℝ) := by
      apply Real.log_le_log (by positivity)
      have hmk : m≤k := by dsimp [m]; exact Nat.div_le_self k (2*R)
      exact_mod_cast hmk
    have hqlog := (nativeEntropyCrossing_log_bounds hd hmpos).2
    have hnlog : (N:ℝ)+1 ≤ L*Real.log (k:ℝ) := by
      have hqcast : (N:ℝ)=2*((q:ℝ)-1) := by
        dsimp [N]
        simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 1≤q)]
        push_cast
        ring
      have hqlog' : (q:ℝ)≤Q*Real.log (k:ℝ) := by
        have hqlogm : (q:ℝ)≤Q*Real.log (m:ℝ) := by
          simpa [q,Q,nativeLogScaleUpper] using hqlog
        exact hqlogm.trans (mul_le_mul_of_nonneg_left hlogm
          (le_of_lt (nativeLogScaleUpper_pos hd)))
      rw [hqcast]
      dsimp [L]
      have hlogpos : 1≤Real.log (k:ℝ) := by
        have hkexp : Real.exp 1 ≤ (k:ℝ) := by
          have hk3 : 3≤k := by omega
          have h3 : Real.exp 1<3 := Real.exp_one_lt_three
          exact h3.le.trans (by exact_mod_cast hk3)
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hkexp
      nlinarith [hqlog']
    have hlogpos : 1≤Real.log (k:ℝ) := by
      have hk3 : 3≤k := by omega
      have hkexp : Real.exp 1 ≤ (k:ℝ) := by
        have h3 : Real.exp 1<3 := Real.exp_one_lt_three
        exact h3.le.trans (by exact_mod_cast hk3)
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hkexp
    have hnpoly : ((N:ℝ)+1)^F ≤ (L*Real.log (k:ℝ))^F := by
      apply Real.rpow_le_rpow
      · positivity
      · exact hnlog
      · dsimp [F]
        positivity
    have hU : U = 16*(R:ℝ)*(d:ℝ)^2*L^F := rfl
    have hmLower : (k:ℝ)/(4*(R:ℝ)) ≤ (m:ℝ) := by
      have hfloor : k < 2*R*(m+1) := by
        have hrem := Nat.mod_lt k (by omega : 0<2*R)
        have hdecomp := Nat.mod_add_div k (2*R)
        have hremR : ((k % (2*R):ℕ):ℝ) < (2*R:ℝ) := by exact_mod_cast hrem
        have hdecompR : ((k % (2*R):ℕ):ℝ) + (2*R:ℝ)*(k/(2*R):ℕ) = (k:ℝ) := by
          exact_mod_cast hdecomp
        have hmcast : (m:ℝ)=(k/(2*R):ℕ) := by rfl
        have hreal : (k:ℝ) < 2*(R:ℝ)*((m:ℝ)+1) := by
          rw [hmcast]
          nlinarith [hremR,hdecompR]
        exact_mod_cast hreal
      have hRpos : 0<(R:ℝ) := by exact_mod_cast hR
      have h : (k:ℝ)<2*(R:ℝ)*((m:ℝ)+1) := by exact_mod_cast hfloor
      have hmR : 1≤(m:ℝ) := by exact_mod_cast (by omega : 1≤m)
      apply (div_le_iff₀ (by positivity : 0<(4:ℝ)*(R:ℝ))).2
      nlinarith
    have hscaleUpper : (2:ℝ)^(-(N:ℝ)) ≤ U*((Real.log (k:ℝ))^F)/(k:ℝ) := by
      have hLpos : 0<L := by
        dsimp [L,Q]
        have hQ := nativeLogScaleUpper_pos hd
        positivity
      have hlogpos' : 0<Real.log (k:ℝ) := by linarith [hlogpos]
      have hlog' : ((N:ℝ)+1)^F ≤ L^F*(Real.log (k:ℝ))^F := by
        have hfactor : (L*Real.log (k:ℝ))^F = L^F*(Real.log (k:ℝ))^F := by
          rw [Real.mul_rpow hLpos.le hlogpos'.le]
        rw [hfactor] at hnpoly
        exact hnpoly
      have hminv : 1/(m:ℝ) ≤ 4*(R:ℝ)/(k:ℝ) := by
        have hkRpos : 0<(k:ℝ) := by positivity
        have hRpos : 0<(R:ℝ) := by norm_cast
        have hmMul : (k:ℝ) ≤ 4*(R:ℝ)*(m:ℝ) :=
          by simpa [mul_comm] using
            (div_le_iff₀ (by positivity : 0<4*(R:ℝ))).1 hmLower
        have hmRpos : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
        have hcross : 1*(k:ℝ) ≤ (4*(R:ℝ))*(m:ℝ) := by simpa using hmMul
        exact (div_le_div_iff₀ hmRpos hkRpos).2 hcross
      calc
        (2:ℝ)^(-(N:ℝ)) ≤ (4*(d:ℝ)^2)*((N:ℝ)+1)^F/(m:ℝ) := hdyadic
        _ ≤ (4*(d:ℝ)^2)*(L^F*(Real.log (k:ℝ))^F)*(4*(R:ℝ))/(k:ℝ) := by
          have hp := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog' (by positivity : 0≤(4:ℝ)*(d:ℝ)^2))
            (by positivity : 0≤1/(m:ℝ))
          have hq := mul_le_mul_of_nonneg_left hminv
            (mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg hLpos.le F)
              (Real.rpow_nonneg hlogpos'.le F)))
          calc
            (4*(d:ℝ)^2)*((N:ℝ)+1)^F/(m:ℝ) =
                (4*(d:ℝ)^2)*((N:ℝ)+1)^F*(1/(m:ℝ)) := by ring
            _ ≤ (4*(d:ℝ)^2)*(L^F*(Real.log (k:ℝ))^F)*(1/(m:ℝ)) := by
              simpa [div_eq_mul_inv, mul_assoc] using hp
            _ ≤ (4*(d:ℝ)^2)*(L^F*(Real.log (k:ℝ))^F)*(4*(R:ℝ)/(k:ℝ)) := by nlinarith [hq]
            _ = (4*(d:ℝ)^2)*(L^F*(Real.log (k:ℝ))^F)*(4*(R:ℝ))/(k:ℝ) := by ring
        _ = U*((Real.log (k:ℝ))^F)/(k:ℝ) := by dsimp [U]; field_simp; ring
    have hpowrate : ((2:ℝ)^(-(N:ℝ)))^β ≤
        (U*((Real.log (k:ℝ))^F)/(k:ℝ))^β :=
      Real.rpow_le_rpow (by positivity) hscaleUpper hβ.le
    have hpowid : ((2:ℝ)^(-(N:ℝ)))^β = (2:ℝ)^(-β*(N:ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      congr 1 <;> ring
    have htarget : A*(2:ℝ)^(-β*(N:ℝ)) ≤
        C*(k:ℝ)^(-β)*(Real.log (k:ℝ))^(β*F) := by
      rw [← hpowid]
      have hfactor : (U*((Real.log (k:ℝ))^F)/(k:ℝ))^β =
          U^β*(k:ℝ)^(-β)*(Real.log (k:ℝ))^(β*F) := by
        have hUpos : 0<U := by
          dsimp [U,L,Q]
          have hQ := nativeLogScaleUpper_pos hd
          positivity
        have hkposR : 0<(k:ℝ) := by positivity
        have hlogR : 0<Real.log (k:ℝ) := by linarith [hlogpos]
        have hVpos : 0 < (Real.log (k:ℝ))^F := by positivity
        calc
          (U*((Real.log (k:ℝ))^F)/(k:ℝ))^β =
              (U*((Real.log (k:ℝ))^F))^β/(k:ℝ)^β :=
            Real.div_rpow (le_of_lt (mul_pos hUpos hVpos)) hkposR.le β
          _ = U^β*((Real.log (k:ℝ))^F)^β/(k:ℝ)^β := by
            rw [Real.mul_rpow (le_of_lt hUpos) (le_of_lt hVpos)]
          _ = U^β*(k:ℝ)^(-β)*(Real.log (k:ℝ))^(β*F) := by
            have hlogpow : ((Real.log (k:ℝ))^F)^β =
                (Real.log (k:ℝ))^(β*F) := by
              calc
                ((Real.log (k:ℝ))^F)^β = (Real.log (k:ℝ))^(F*β) :=
                  (Real.rpow_mul (le_of_lt hlogR) F β).symm
                _ = (Real.log (k:ℝ))^(β*F) := by congr 1 <;> ring
            have hkpow : ((k:ℝ)^β)⁻¹=(k:ℝ)^(-β) := by
              rw [Real.rpow_neg (by positivity)]
            rw [hlogpow, div_eq_mul_inv, hkpow]
            ring
      rw [hfactor] at hpowrate
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_left hpowrate (le_of_lt hA)]
    have hbound := hlayer N hN0
    have hf := hfmono hindex
    exact hf.trans (hbound.trans (ENNReal.ofReal_le_ofReal htarget))

/-- The layer dimension absorbs one dyadic factor and the polynomial grade
factor, which is the numeric step behind the Hilbert--Schmidt tail estimate. -/
theorem weighted_tail_div_layer_le
    {d N : ℕ} (hd : 2 ≤ d) (B β : ℝ) (hB : 0 ≤ B)
    (hβ : 0 < β) :
    (B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) * ((N:ℝ)+1)^((d-1:ℕ):ℝ)) /
        (Fintype.card (LayerIndex d N):ℝ) ≤
      (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) := by
  have hdim : (2:ℝ)^N * (((N:ℝ)+1)^((d-1:ℕ):ℝ) /
      (Nat.factorial (d-1):ℝ)) ≤
      (Fintype.card (LayerIndex d N):ℝ) := by
    have hcount := hyperbolicCount_lower_shift (d:=d) (by omega : 1≤d) N
    have hcount' : ((N:ℝ)+1)^((d-1:ℕ):ℝ) /
        (Nat.factorial (d-1):ℝ) ≤ hyperbolicCount d N := by
      simpa [Real.rpow_natCast] using hcount
    have hdim' : nativeDimension d N ≤ (Fintype.card (LayerIndex d N):ℝ) := by
      have hcard : (Fintype.card (LayerIndex d N):ℝ)=nativeDimension d N := by
        rw [layerIndex_card d N (by omega : 0<d)]
        simp [nativeDimension,hyperbolicCount]
      rw [hcard]
    have hidentity : nativeDimension d N =
        (2:ℝ)^N * hyperbolicCount d N := rfl
    rw [hidentity] at hdim'
    have hpnonneg : 0≤(2:ℝ)^N := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcount' hpnonneg
    exact hmul.trans hdim'
  have hfactpos : 0 < (Nat.factorial (d-1):ℝ) := by positivity
  have hpowpos : 0 < (2:ℝ)^N := by positivity
  have hpolypos : 0 < ((N:ℝ)+1)^((d-1:ℕ):ℝ) := by positivity
  have hdimpos : 0 < (Fintype.card (LayerIndex d N):ℝ) := by
    exact (mul_pos hpowpos (div_pos hpolypos hfactpos)).trans_le hdim
  have hmul :
      (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) *
          ((2:ℝ)^N * (((N:ℝ)+1)^((d-1:ℕ):ℝ) /
            (Nat.factorial (d-1):ℝ))) ≤
      (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) *
          ((Fintype.card (LayerIndex d N):ℝ)) := by
    have hc : 0 ≤ B * (Nat.factorial (d-1):ℝ) *
        (2:ℝ)^(-2*β*(N:ℝ)) := by positivity
    have h := mul_le_mul_of_nonneg_left hdim hc
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hpower :
      (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) *
          ((2:ℝ)^N * (((N:ℝ)+1)^((d-1:ℕ):ℝ) /
            (Nat.factorial (d-1):ℝ))) =
        B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) * ((N:ℝ)+1)^((d-1:ℕ):ℝ) := by
    have h2 : (2:ℝ)^(-2*β*(N:ℝ))*(2:ℝ)^N =
        (2:ℝ)^(-((2*β-1)*(N:ℝ))) := by
      rw [(Real.rpow_natCast (2:ℝ) N).symm]
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1 <;> ring
    calc
      (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) *
          ((2:ℝ)^N * (((N:ℝ)+1)^((d-1:ℕ):ℝ) /
            (Nat.factorial (d-1):ℝ))) =
        B * (Nat.factorial (d-1):ℝ) *
          ((2:ℝ)^(-2*β*(N:ℝ))*(2:ℝ)^N) *
          (((N:ℝ)+1)^((d-1:ℕ):ℝ)/(Nat.factorial (d-1):ℝ)) := by ring
      _ = B * (Nat.factorial (d-1):ℝ) *
          (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
          (((N:ℝ)+1)^((d-1:ℕ):ℝ)/(Nat.factorial (d-1):ℝ)) := by rw [h2]
      _ = B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
          ((N:ℝ)+1)^((d-1:ℕ):ℝ) := by
        field_simp
  have hcross :
      B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) * ((N:ℝ)+1)^((d-1:ℕ):ℝ) ≤
        (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-2*β*(N:ℝ)) *
          ((Fintype.card (LayerIndex d N):ℝ)) := by
    rw [← hpower]
    exact hmul
  apply (div_le_iff₀ hdimpos).2
  nlinarith [hcross]

end BrownianSharp.AlignmentTensorApproximationUpperRate
