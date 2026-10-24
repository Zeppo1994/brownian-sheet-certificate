import BrownianSharp.AlignmentFractionalApproximationUpper
import BrownianSharp.AlignmentEndpointWidthExtraction
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.ExtendedStatements
import BrownianSharp.LayerIndex
import BrownianSharp.ShapeGrowth
import BrownianSharp.PeriodicEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open BrownianSharp HaarQuarter Filter
open scoped ENNReal Topology
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

namespace BrownianSharp.AlignmentFractionalApproximationRates

noncomputable section

open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentEndpointWidthExtraction
open BrownianSharp.AlignmentFractionalApproximationUpper
open BrownianSharp.AlignmentFractionalTensorOperator
open HaarQuarter.TheoremD.Width

/-- Strict-rank approximation numbers decrease as the allowed rank increases. -/
private theorem iInf_subtype_mono {ι α : Type*} [CompleteLattice α]
    (p q : ι → Prop) (f : ι → α) (hpq : ∀ i, p i → q i) :
    (⨅ i : {i // q i}, f i.1) ≤ ⨅ i : {i // p i}, f i.1 := by
  apply le_iInf
  intro i
  exact iInf_le (fun j : {j // q j} => f j.1) ⟨i.1, hpq i.1 i.2⟩

theorem approximationNumber_antitone
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) {k m : ℕ} (hkm : k ≤ m) :
    approximationNumber T m ≤ approximationNumber T k := by
  unfold approximationNumber
  change (⨅ A : {A : X →L[ℝ] Y //
      Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (m : Cardinal)},
      ENNReal.ofReal ‖T-A.1‖) ≤
    ⨅ A : {A : X →L[ℝ] Y //
      Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal)},
      ENNReal.ofReal ‖T-A.1‖
  exact iInf_subtype_mono
    (fun A : X →L[ℝ] Y => Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal))
    (fun A : X →L[ℝ] Y => Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (m : Cardinal))
    (fun A : X →L[ℝ] Y => ENNReal.ofReal ‖T-A‖)
    (fun A hA => lt_of_lt_of_le hA (by exact_mod_cast hkm))

private theorem crossing_eventually_ge {d N : ℕ} (hd : 2 ≤ d) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      N ≤ nativeEntropyCrossing d k (by omega) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : 0 < nativeLogScaleLower d := nativeLogScaleLower_pos hd
  have hev : ∀ᶠ k : ℕ in atTop,
      N ≤ nativeEntropyCrossing d k (by omega) := by
    filter_upwards [hlog.eventually_ge_atTop
      (nativeLogScaleLower d * (N : ℝ)), eventually_ge_atTop 2] with k hlarge hk
    rw [nativeLogScaleLower] at hlarge
    have hcross := (nativeEntropyCrossing_log_bounds hd hk).1
    have hN : (N : ℝ) ≤ (nativeEntropyCrossing d k (by omega) : ℝ) := by
      apply (mul_le_mul_iff_of_pos_left hscale).1
      exact hlarge.trans hcross
    exact_mod_cast hN
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  exact ⟨max 2 k₀, le_max_left _ _, fun k hk =>
    hk₀ k ((le_max_right _ _).trans hk)⟩

/-- Convert any eventual dyadic hyperbolic-layer width bound into its sharp
all-index rate for strict-rank bounded-linear approximation numbers. The spatial
exponent and polynomial layer loss are parameters; `A` is the fixed rank multiplier. -/
theorem approximationNumber_all_index_rate_of_dyadic_layer_bound
    {d : ℕ} (hd : 2 ≤ d) {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) (A : ℕ) (hA : 0 < A)
    (r a B : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (hB : 0 < B) (n₀ : ℕ)
    (hupper : ∀ n : ℕ, n₀ ≤ n →
      approximationNumber T (A * Fintype.card (LayerIndex d n) + 1) ≤
        ENNReal.ofReal (B * (2 : ℝ) ^ (-r * (n : ℝ)) *
          ((n : ℝ) + 1) ^ a)) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₁ : ℕ, 8 * A ≤ m₁ ∧
      ∀ m : ℕ, m₁ ≤ m →
        approximationNumber T m ≤
          ENNReal.ofReal (C * logarithmicIndexRate r
            (r * ((d - 1 : ℕ) : ℝ) + a) m) := by
  let α : ℝ := r * ((d - 1 : ℕ) : ℝ) + a
  let Q : ℝ := nativeLogScaleUpper d
  let L : ℝ := 2 * Q + 1
  let D₀ : ℝ := 32 * (A : ℝ) * (d : ℝ) ^ 2
  let C : ℝ := B * D₀ ^ r * L ^ α
  obtain ⟨k₀,hk₀,hcross⟩ := crossing_eventually_ge (d:=d) (N:=n₀+1) hd
  let m₀ : ℕ := max (8*A) (4*A*k₀)
  refine ⟨C,?_,m₀,?_,?_⟩
  · dsimp [C,D₀,L,Q]
    have hL : 0 < 2*nativeLogScaleUpper d+1 := by
      have hQ := nativeLogScaleUpper_pos hd
      positivity
    have hD₀ : 0 < (32:ℝ)*(A:ℝ)*(d:ℝ)^2 := by
      have hAR : 0 < (A:ℝ) := by exact_mod_cast hA
      have hdR : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0<d)
      positivity
    exact mul_pos (mul_pos hB (Real.rpow_pos_of_pos hD₀ _))
      (Real.rpow_pos_of_pos hL _)
  · dsimp [m₀]
    omega
  · intro m hm
    have hma : 8*A ≤ m := by dsimp [m₀] at hm; omega
    let k : ℕ := m / (4*A)
    have hk : 2 ≤ k := by
      have hden : 0 < 4*A := by omega
      have hmul : 2*(4*A) ≤ m := by omega
      dsimp [k]
      exact (Nat.le_div_iff_mul_le hden).2 (by simpa [Nat.mul_comm] using hmul)
    have hk₀m : k₀ ≤ k := by
      have hmul : 4*A*k₀ ≤ m := by
        have : 4*A*k₀ ≤ m₀ := by dsimp [m₀]; omega
        exact this.trans hm
      dsimp [k]
      exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_comm] using hmul)
    let q : ℕ := nativeEntropyCrossing d k (by omega)
    have hqgrade : n₀+1 ≤ q := by
      simpa [q,k] using hcross k hk₀m
    have hbr := nativeEntropyCrossing_bracket hd hk
    have hqpos : 0<q := by simpa [q] using hbr.1
    let n : ℕ := 2*(q-1)
    have hn : n₀≤n := by dsimp [n]; omega
    have hprev : nativeDimension d n < (k:ℝ) := by simpa [n,q] using hbr.2.1
    have hq1 : 1≤q := hqpos
    have hn2 : n+2=2*q := by dsimp [n]; omega
    have hcurr : (k:ℝ)≤nativeDimension d (n+2) := by rw [hn2]; exact hbr.2.2.1
    have hstep₁ := nativeDimension_step_le (d:=d) (n:=n) (by omega)
    have hstep₂ := nativeDimension_step_le (d:=d) (n:=n+1) (by omega)
    have hdimstep : nativeDimension d (n+2) ≤
        (4*(d:ℝ)^2)*nativeDimension d n := by
      calc
        nativeDimension d (n+2) ≤ (2*(d:ℝ))*nativeDimension d (n+1) := by
          simpa [Nat.add_assoc] using hstep₂
        _ ≤ (2*(d:ℝ))*((2*(d:ℝ))*nativeDimension d n) :=
          mul_le_mul_of_nonneg_left hstep₁ (by positivity)
        _ = (4*(d:ℝ)^2)*nativeDimension d n := by ring
    have hdimlower0 : (k:ℝ)/(4*(d:ℝ)^2) ≤ nativeDimension d n := by
      have hdpos : 0<(4:ℝ)*(d:ℝ)^2 := by positivity
      apply (div_le_iff₀ hdpos).2
      calc
        (k:ℝ)≤nativeDimension d (n+2) := hcurr
        _≤(4*(d:ℝ)^2)*nativeDimension d n := hdimstep
        _=nativeDimension d n*(4*(d:ℝ)^2) := by ring
    have hk_m : (m:ℝ)/(8*(A:ℝ)) ≤ (k:ℝ) := by
      have hdiv : (m:ℝ)<4*(A:ℝ)*(k:ℝ)+4*(A:ℝ) := by
        have hden : 0 < 4*A := by omega
        have hrem := Nat.mod_lt m hden
        have hdecomp := Nat.mod_add_div m (4*A)
        have hnat : m < 4*A*(m/(4*A)+1) := by nlinarith [hdecomp,hrem]
        exact_mod_cast hnat
      have hkpos : 1≤k := by omega
      have hkR : 1≤(k:ℝ) := by exact_mod_cast hkpos
      have hAR : 0<(A:ℝ) := by exact_mod_cast hA
      have hmR : 0≤(m:ℝ) := by positivity
      have hbound : (m:ℝ) ≤ 8*(A:ℝ)*(k:ℝ) := by
        have hprod : 0≤(4*(A:ℝ))*((k:ℝ)-1) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith [hdiv,hprod]
      have hbound' : (m:ℝ)≤(k:ℝ)*(8*(A:ℝ)) := by nlinarith [hbound]
      exact (div_le_iff₀ (by positivity : 0<8*(A:ℝ))).2 hbound'
    have hDlower : (m:ℝ)/D₀ ≤ nativeDimension d n := by
      have hmul := div_le_div_of_nonneg_right hk_m
        (by positivity : 0≤(4:ℝ)*(d:ℝ)^2)
      have hsimp : ((m:ℝ)/(8*(A:ℝ)))/(4*(d:ℝ)^2)=
          (m:ℝ)/D₀ := by dsimp [D₀]; field_simp; ring
      rw [hsimp] at hmul
      exact hmul.trans hdimlower0
    have hDpos : 0<nativeDimension d n := by
      have hD₀pos : 0<D₀ := by dsimp [D₀]; positivity
      have hmpos : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
      exact (div_pos hmpos hD₀pos).trans_le hDlower
    have hcard : (Fintype.card (LayerIndex d n):ℝ)=nativeDimension d n := by
      rw [layerIndex_card d n (by omega)]
      simp [nativeDimension,hyperbolicCount]
    have hrank : A*Fintype.card (LayerIndex d n) + 1 ≤ m := by
      have hprev' : (Fintype.card (LayerIndex d n):ℝ)<(k:ℝ) := by
        rw [hcard]
        exact hprev
      have hprevNat : Fintype.card (LayerIndex d n)<k := by exact_mod_cast hprev'
      have hAk : A*k ≤ m := by
        have hdivmul : k*(4*A) ≤ m := by
          dsimp [k]
          exact Nat.div_mul_le_self m (4*A)
        have hA4 : A≤4*A := by omega
        have hsmall : A*k≤(4*A)*k := Nat.mul_le_mul_right k hA4
        have hdivmul' : (4*A)*k≤m := by simpa [Nat.mul_comm] using hdivmul
        exact hsmall.trans hdivmul'
      have hAc : A*Fintype.card (LayerIndex d n) < A*k := Nat.mul_lt_mul_of_pos_left hprevNat hA
      exact (Nat.succ_le_of_lt hAc).trans hAk
    have hwidth := hupper n hn
    have hdyadicId : (2:ℝ)^(-r*(n:ℝ))=((2:ℝ)^n)^(-r) := by
      calc
        (2:ℝ)^(-r*(n:ℝ))=(2:ℝ)^((n:ℝ)*(-r)) := by congr 1 <;> ring
        _=((2:ℝ)^n)^(-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [hdyadicId] at hwidth
    have hmono := approximationNumber_antitone T hrank
    have hshape : hyperbolicCount d n ≤ ((n:ℝ)+1)^(d-1) :=
      hyperbolicCount_upper_shift (by omega) n
    have hDidentity : nativeDimension d n=(2:ℝ)^n*hyperbolicCount d n := rfl
    have hlogm : 1≤Real.log (m:ℝ) := by
      have hmexp : Real.exp 1≤(m:ℝ) := by
        have h3 : Real.exp 1<3 := Real.exp_one_lt_three
        have hmR : 3≤(m:ℝ) := by exact_mod_cast (by omega : 3≤m)
        exact h3.le.trans hmR
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hmexp
    have hlogmk : Real.log (k:ℝ)≤Real.log (m:ℝ) := by
      apply Real.log_le_log (by positivity)
      have hdivmul : k*(4*A)≤m := by dsimp [k]; exact Nat.div_mul_le_self m (4*A)
      have hpos : 1≤4*A := by omega
      have hkm : k≤k*(4*A) := Nat.le_mul_of_pos_right k hpos
      have : k≤m := le_trans hkm hdivmul
      exact_mod_cast this
    have hqlog := (nativeEntropyCrossing_log_bounds hd hk).2
    have hqlog' : (q:ℝ)≤Q*Real.log (m:ℝ) := by
      have hqeq : q=nativeEntropyCrossing d k (by omega) := rfl
      rw [hqeq]
      calc
        (nativeEntropyCrossing d k (by omega):ℝ)≤nativeLogScaleUpper d*Real.log (k:ℝ) := hqlog
        _≤Q*Real.log (m:ℝ) := by
          simpa [Q] using mul_le_mul_of_nonneg_left hlogmk
            (le_of_lt (nativeLogScaleUpper_pos hd))
    have hnlog : (n:ℝ)+1≤L*Real.log (m:ℝ) := by
      have hqcast : (n:ℝ)=2*((q:ℝ)-1) := by
        dsimp [n]
        simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 1≤q)]
        push_cast
        ring
      rw [hqcast]
      dsimp [L]
      have hQpos : 0≤Q := le_of_lt (nativeLogScaleUpper_pos hd)
      nlinarith [hqlog',hlogm]
    have hα : 0≤α := by dsimp [α]; positivity
    have hbasepos : 0<L*Real.log (m:ℝ) := by
      have hLpos : 0<L := by
        dsimp [L,Q]
        have hQ := nativeLogScaleUpper_pos hd
        positivity
      exact mul_pos hLpos (by linarith)
    have hnpow : ((n:ℝ)+1)^α≤(L*Real.log (m:ℝ))^α :=
      Real.rpow_le_rpow (by positivity) hnlog hα
    have hfactor : (L*Real.log (m:ℝ))^α=
        L^α*(Real.log (m:ℝ))^α := by
      have hLpos : 0<L := by
        dsimp [L,Q]
        have hQ := nativeLogScaleUpper_pos hd
        positivity
      have hlogpos : 0<Real.log (m:ℝ) := by linarith
      rw [Real.mul_rpow hLpos.le hlogpos.le]
    have hsqrtShape : (((n:ℝ)+1)^((d-1:ℕ):ℝ))^r*((n:ℝ)+1)^a=
        ((n:ℝ)+1)^α := by
      rw [← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_add (by positivity)]
      congr 1
      dsimp [α]
      rw [Nat.cast_sub (by omega : 1≤d)]
      ring
    have hbaseDiv : ((2:ℝ)^n)^(-r) ≤
        ((n:ℝ)+1)^((r*((d-1:ℕ):ℝ))) / (nativeDimension d n)^r := by
      have hS : 0<hyperbolicCount d n := hyperbolicCount_pos (by omega)
      have hSle : (hyperbolicCount d n:ℝ)≤((n:ℝ)+1)^(d-1) := hshape
      have hpow : (2:ℝ)^n = nativeDimension d n / hyperbolicCount d n := by
        rw [hDidentity]
        field_simp
      have hinv : ((2:ℝ)^n)⁻¹ ≤ ((n:ℝ)+1)^((d-1:ℕ):ℝ) / nativeDimension d n := by
        rw [hpow]
        have hT : (hyperbolicCount d n:ℝ)≤((n:ℝ)+1)^((d-1:ℕ):ℝ) := by
          calc
            (hyperbolicCount d n:ℝ) ≤ ((n:ℝ)+1)^(d-1) := hSle
            _ = ((n:ℝ)+1)^((d-1:ℕ):ℝ) := by rw [← Real.rpow_natCast]
        have hDpos' : 0<nativeDimension d n := hDpos
        apply (le_div_iff₀ hDpos').2
        have heq : (nativeDimension d n / (hyperbolicCount d n:ℝ))⁻¹ *
            nativeDimension d n = hyperbolicCount d n := by field_simp
        rw [heq]
        exact hT
      have hpowr := Real.rpow_le_rpow (by positivity) hinv hr.le
      have hinvpow : (((2:ℝ)^n)⁻¹)^r=((2:ℝ)^n)^(-r) := by
        rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
      rw [← hinvpow]
      calc
        _≤ (((n:ℝ)+1)^((d-1:ℕ):ℝ)/nativeDimension d n)^r := hpowr
        _ = ((n:ℝ)+1)^((r*((d-1:ℕ):ℝ)))/(nativeDimension d n)^r := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
          congr 1
          ring
    have hDpow : (nativeDimension d n)^(-r)≤(D₀/(m:ℝ))^r := by
      have hDinv : (nativeDimension d n)⁻¹≤D₀/(m:ℝ) := by
        have hD₀pos : 0<D₀ := by dsimp [D₀]; positivity
        have hmpos : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
        calc
          (nativeDimension d n)⁻¹ ≤ 1/((m:ℝ)/D₀) := by
            simpa [one_div] using
              (one_div_le_one_div hDpos (div_pos hmpos hD₀pos)).2 hDlower
          _ = D₀/(m:ℝ) := by field_simp
      have hpow := Real.rpow_le_rpow (by positivity) hDinv hr.le
      have hleft : (nativeDimension d n)⁻¹^r=(nativeDimension d n)^(-r) := by
        rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
      rw [← hleft]
      exact hpow
    have hrate_real : B*((2:ℝ)^n)^(-r)*((n:ℝ)+1)^a ≤
        C*logarithmicIndexRate r α m := by
      have hmpos : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
      have hcoefpos : 0≤B := hB.le
      have hdyadic : ((2:ℝ)^n)^(-r)*((n:ℝ)+1)^a ≤
          (((n:ℝ)+1)^α)*(nativeDimension d n)^(-r) := by
        have htmp : ((n:ℝ)+1)^(r*((d-1:ℕ):ℝ))*((n:ℝ)+1)^a=
            ((n:ℝ)+1)^α := by
          rw [← Real.rpow_add (by positivity)]
        calc
          _ ≤ (((n:ℝ)+1)^(r*((d-1:ℕ):ℝ))/nativeDimension d n^r)*((n:ℝ)+1)^a :=
            mul_le_mul_of_nonneg_right hbaseDiv (by positivity)
        _ = (((n:ℝ)+1)^α)*(nativeDimension d n)^(-r) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), ← htmp]
            ring
      have hrate0 : B*((2:ℝ)^n)^(-r)*((n:ℝ)+1)^a ≤
          B*((n:ℝ)+1)^α*(nativeDimension d n)^(-r) := by
        calc
          _ = B*(((2:ℝ)^n)^(-r)*((n:ℝ)+1)^a) := by ring
          _ ≤ B*(((n:ℝ)+1)^α*(nativeDimension d n)^(-r)) :=
            mul_le_mul_of_nonneg_left hdyadic hB.le
          _ = _ := by ring
      have hrate1 : B*((n:ℝ)+1)^α*(nativeDimension d n)^(-r) ≤
          B*((n:ℝ)+1)^α*(D₀/(m:ℝ))^r :=
        mul_le_mul_of_nonneg_left hDpow (by positivity)
      have hpowfac : (D₀/(m:ℝ))^r=D₀^r*(m:ℝ)^(-r) := by
        rw [Real.div_rpow (by positivity) (by positivity), div_eq_mul_inv,
          ← Real.rpow_neg (by positivity)]
      have hnpow' : ((n:ℝ)+1)^α≤L^α*(Real.log (m:ℝ))^α := hnpow.trans_eq hfactor
      dsimp [C,logarithmicIndexRate]
      calc
        _ ≤ B*((n:ℝ)+1)^α*(D₀/(m:ℝ))^r := hrate0.trans hrate1
        _ = B*((n:ℝ)+1)^α*(D₀^r*(m:ℝ)^(-r)) := by rw [hpowfac]
        _ ≤ B*(L^α*(Real.log (m:ℝ))^α)*(D₀^r*(m:ℝ)^(-r)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hnpow' hB.le
          · positivity
        _ = (B*D₀^r*L^α)*((m:ℝ)^(-r)*(Real.log (m:ℝ))^α) := by ring
      -- The final expression unfolds to the claimed logarithmic rate.
    have hwidth' : approximationNumber T m ≤
        ENNReal.ofReal (C*logarithmicIndexRate r α m) := by
      exact hmono.trans (hwidth.trans (ENNReal.ofReal_le_ofReal hrate_real))
    simpa [α,cmIndexRate,logarithmicIndexRate] using hwidth'

private theorem sqrt_fractional_profile_eq {d : ℕ} (hd : 1 ≤ d) (r : ℝ)
    (hr : 1/2 < r) (n : ℕ) :
    Real.sqrt ((Real.rpow 2 (-(2*r-1)))^n *
        ((n+1:ℕ):ℝ)^(d-1)) =
      (2:ℝ)^(-(r-1/2)*(n:ℝ)) *
        ((n+1:ℕ):ℝ)^(((d-1:ℕ):ℝ)/2) := by
  let ρ : ℝ := Real.rpow 2 (-(2*r-1))
  let x : ℝ := ((n+1:ℕ):ℝ)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hρpow : 0 ≤ ρ^n := pow_nonneg hρ.le _
  have hxpow : 0 ≤ x^(d-1) := pow_nonneg hx.le _
  rw [Real.sqrt_eq_rpow]
  rw [Real.mul_rpow hρpow hxpow]
  rw [← Real.rpow_natCast ρ n, ← Real.rpow_mul hρ.le]
  rw [← Real.rpow_natCast x (d-1), ← Real.rpow_mul hx.le]
  dsimp [ρ, x]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  · congr 1
    ring
  · congr 1
    rw [Nat.cast_sub hd]
    ring

/-- Actual all-index bounded-linear approximation upper bound for the
fractional tensor RL operator. The dyadic profile has spatial exponent
`r-1/2` and polynomial loss `(ν-1)/2`; hyperbolic rank conversion yields the
logarithmic exponent `r(ν-1)`. -/
theorem polynomial_fractional_tensor_RL_approximation_number_upper
    {ν e : ℕ} (hν : 2 ≤ ν) {r : ℝ} (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ A : ℕ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∃ k₀ : ℕ, 8 * A ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        approximationNumber (fractionalTensorRL α hα) k ≤
          ENNReal.ofReal (C * logarithmicIndexRate (r-1/2)
            (r*((ν-1:ℕ):ℝ)) k) := by
  obtain ⟨A,hA,B,hB,hdyadic⟩ :=
    polynomial_fractional_tensor_RL_approximation_number_dyadic hν hr α hα hm
  have hs : 0 < r-1/2 := by linarith
  have ha : 0 ≤ ((ν-1:ℕ):ℝ)/2 := by positivity
  have hupper : ∀ n : ℕ, 0 ≤ n →
      approximationNumber (fractionalTensorRL α hα)
          (A * Fintype.card (LayerIndex ν n) + 1) ≤
        ENNReal.ofReal (B * (2:ℝ)^(-(r-1/2)*(n:ℝ)) *
          ((n:ℝ)+1)^(((ν-1:ℕ):ℝ)/2)) := by
    intro n hn
    have heq := sqrt_fractional_profile_eq (by omega : 1 ≤ ν) r hr n
    have hdyn := hdyadic n
    rw [heq] at hdyn
    simpa [mul_assoc] using hdyn
  obtain ⟨C,hC,k₀,hk₀,hbound⟩ :=
    approximationNumber_all_index_rate_of_dyadic_layer_bound
      (d:=ν) hν (fractionalTensorRL α hα) A hA (r-1/2)
      (((ν-1:ℕ):ℝ)/2) B hs ha hB 0 hupper
  refine ⟨A,hA,C,hC,k₀,?_,?_⟩
  · exact hk₀
  · intro k hk
    have hparam : (r-1/2)*((ν-1:ℕ):ℝ)+((ν-1:ℕ):ℝ)/2 =
        r*((ν-1:ℕ):ℝ) := by ring
    have hb := hbound k hk
    rw [hparam] at hb
    exact hb

end
end BrownianSharp.AlignmentFractionalApproximationRates
