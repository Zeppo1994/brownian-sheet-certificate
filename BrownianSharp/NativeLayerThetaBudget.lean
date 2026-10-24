import BrownianSharp.NativeLayerBudget
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Powered-block summability utilities. The source-coordinate estimate is the
uniform geometric convolution needed for the `theta ≥ 2` Besov branch; unlike
the fixed-grade l1 estimate it sums over every possible source depth. -/

noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 500000

namespace BrownianSharp.NativeLayerThetaBudget

open BrownianSharp.LayerBlockSummability
open BrownianSharp.ScalarVariancePointwise
open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.NativeLayerBudget
open BrownianSharp.NativeLayerSummability

/-- Finite-shape subadditivity for powers in the concave range. -/
theorem finset_sum_rpow_le_sum_rpow {α : Type*} (s : Finset α)
    (f : α → ℝ≥0∞) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∑ a ∈ s, f a) ^ u ≤ ∑ a ∈ s, (f a ^ u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hu0]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        (f a + ∑ x ∈ s, f x) ^ u ≤ f a ^ u + (∑ x ∈ s, f x) ^ u :=
          ENNReal.rpow_add_le_add_rpow (f a) (∑ x ∈ s, f x) hu0.le hu1
        _ = (∑ x ∈ s, f x) ^ u + f a ^ u := add_comm _ _
        _ ≤ (∑ x ∈ s, f x ^ u) + f a ^ u := add_le_add_left ih (f a ^ u)
        _ = f a ^ u + ∑ x ∈ s, f x ^ u := add_comm _ _

/-- Tonelli factorization of a product profile over a finite-dimensional
countable product. -/
theorem ennreal_tsum_pi_prod (d : ℕ) (f : Fin d → ℕ → ℝ≥0∞) :
    (∑' t : Fin d → ℕ, ∏ i : Fin d, f i (t i)) =
      ∏ i : Fin d, ∑' k : ℕ, f i k := by
  classical
  induction d with
  | zero => simp
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d+1) => ℕ)
      have heq : (∑' t : Fin (d+1) → ℕ, ∏ i : Fin (d+1), f i (t i)) =
          ∑' p : ℕ × (Fin d → ℕ),
            f 0 p.1 * ∏ i : Fin d, f i.succ (p.2 i) := by
        rw [← e.tsum_eq]
        congr 1
        funext p
        simp [e, Fin.consEquiv, Fin.prod_univ_succ]
      rw [heq, ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ih (fun i k => f i.succ k)]
      rw [ENNReal.tsum_mul_right]
      simp [Fin.prod_univ_succ]

/-- Source-normalized scalar variance. -/
def sourceNormalizedVariance (r : ℝ) (K : ℕ) (C : ℝ) (s k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ((k : ℝ) - (s : ℝ))) *
    scalarVarianceEnvelope K C s k)

/-- Reverse low/high geometric summation. The split is at the target depth
`k`: coarser source levels lie in the low-frequency side, while finer source
levels lie in the high-frequency tail. -/
theorem reverseTsum_le_of_pointwise_split
    (k : ℕ) (qlow qhigh A B : ℝ≥0∞) (hqlo : qlow < 1) (hqhi : qhigh < 1)
    (f : ℕ → ℝ≥0∞)
    (hlow : ∀ s, k ≤ s → f s ≤ A * qlow ^ (s - k))
    (hhigh : ∀ s, s < k → f s ≤ B * qhigh ^ (k - s)) :
    (∑' s : ℕ, f s) ≤ A * (1-qlow)⁻¹ + B * (qhigh * (1 - qhigh)⁻¹) := by
  let low : ℕ → ℝ≥0∞ := fun s => if k ≤ s then A * qlow ^ (s-k) else 0
  let high : ℕ → ℝ≥0∞ := fun s => if s < k then B * qhigh ^ (k-s) else 0
  have hpoint : ∀ s, f s ≤ low s + high s := by
    intro s
    by_cases hs : k ≤ s
    · have hnot : ¬ s < k := by omega
      simpa [low, high, hs, hnot] using hlow s hs
    · have hsk : s < k := Nat.lt_of_not_ge hs
      simp [low, high, hs, hsk]
      exact hhigh s hsk
  have hsum := ENNReal.tsum_le_tsum hpoint
  have hlow_id : (∑' s : ℕ, low s) =
      A * ∑' s : {s : ℕ // k ≤ s}, qlow ^ (s.1-k) := by
    calc
      _ = ∑' s : ℕ, A * (if k ≤ s then qlow^(s-k) else 0) := by
        congr 1; funext s; simp [low]
      _ = A * ∑' s : ℕ, if k ≤ s then qlow^(s-k) else 0 := ENNReal.tsum_mul_left
      _ = A * ∑' s : {s : ℕ // k ≤ s}, qlow^(s.1-k) := by
        congr 1
        have heq : (fun s : ℕ => if k ≤ s then qlow^(s-k) else 0) =
            (Set.Ici k).indicator (fun s => qlow^(s-k)) := by
          funext s; simp [Set.indicator_apply, Set.mem_Ici]
        rw [heq, ← tsum_subtype (Set.Ici k)]
        rfl
  have hlow_bound : (∑' s : ℕ, low s) ≤ A * (1-qlow)⁻¹ := by
    rw [hlow_id]
    have hinj : Function.Injective (fun s : {s : ℕ // k ≤ s} => s.1-k) := by
      intro a b h
      apply Subtype.ext
      change a.1 - k = b.1 - k at h
      have ha := Nat.sub_add_cancel a.2
      have hb := Nat.sub_add_cancel b.2
      calc
        a.1 = (a.1-k)+k := ha.symm
        _ = (b.1-k)+k := by rw [h]
        _ = b.1 := hb
    calc
      A * ∑' s : {s : ℕ // k ≤ s}, qlow^(s.1-k) ≤
          A * ∑' m : ℕ, qlow^m := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun m => qlow^m)
      _ = A * (1-qlow)⁻¹ := by rw [ENNReal.tsum_geometric]
  have hhigh_id : (∑' s : ℕ, high s) =
      B * ∑' s : {s : ℕ // s < k}, qhigh ^ (k-s.1) := by
    calc
      _ = ∑' s : ℕ, B * (if s < k then qhigh^(k-s) else 0) := by
        congr 1; funext s; simp [high]
      _ = B * ∑' s : ℕ, if s < k then qhigh^(k-s) else 0 := ENNReal.tsum_mul_left
      _ = B * ∑' s : {s : ℕ // s < k}, qhigh^(k-s.1) := by
        congr 1
        have heq : (fun s : ℕ => if s < k then qhigh^(k-s) else 0) =
            (Set.Iio k).indicator (fun s => qhigh^(k-s)) := by
          funext s; simp [Set.indicator_apply, Set.mem_Iio]
        rw [heq, ← tsum_subtype (Set.Iio k)]
        rfl
  have hhigh_bound : (∑' s : ℕ, high s) ≤ B * (qhigh * (1-qhigh)⁻¹) := by
    rw [hhigh_id]
    let e : {s : ℕ // s < k} → ℕ := fun s => k-s.1-1
    have hinj : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      dsimp [e] at hab
      omega
    have hexp (s : {s : ℕ // s < k}) : k-s.1 = e s+1 := by
      dsimp [e]; omega
    calc
      B * ∑' s : {s : ℕ // s < k}, qhigh^(k-s.1) =
          B * ∑' s : {s : ℕ // s < k}, qhigh^(e s+1) := by
            congr 2; funext s; rw [hexp]
      _ ≤ B * ∑' m : ℕ, qhigh^(m+1) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun m => qhigh^(m+1))
      _ = B * (qhigh*(1-qhigh)⁻¹) := by rw [ENNReal.tsum_geometric_add_one]
  calc
    _ ≤ (∑' s : ℕ, low s) + ∑' s : ℕ, high s := by
      simpa [ENNReal.tsum_add] using hsum
    _ ≤ A*(1-qlow)⁻¹ + B*(qhigh*(1-qhigh)⁻¹) := add_le_add hlow_bound hhigh_bound

/-- Forward split summation: target levels below a fixed source depth carry
an inclusive geometric tail, while levels above it carry a strict tail. -/
theorem forwardTsum_le_of_pointwise_split
    (s : ℕ) (qlow qhigh A B : ℝ≥0∞) (hqlo : qlow<1) (hqhi : qhigh<1)
    (f : ℕ → ℝ≥0∞)
    (hlow : ∀ k, k≤s → f k≤A*qlow^(s-k))
    (hhigh : ∀ k, s<k → f k≤B*qhigh^(k-s)) :
    (∑' k : ℕ, f k) ≤ A*(1-qlow)⁻¹+B*(qhigh*(1-qhigh)⁻¹) := by
  let low : ℕ → ℝ≥0∞ := fun k => if k≤s then A*qlow^(s-k) else 0
  let high : ℕ → ℝ≥0∞ := fun k => if s<k then B*qhigh^(k-s) else 0
  have hpoint : ∀ k, f k≤low k+high k := by
    intro k
    by_cases hk:k≤s
    · have hnot:¬s<k:=by omega
      simpa [low,high,hk,hnot] using hlow k hk
    · have hsk:s<k:=by omega
      simp [low,high,hk,hsk]
      exact hhigh k hsk
  have hsum:=ENNReal.tsum_le_tsum hpoint
  have hlow_id : (∑' k:ℕ,low k)=A*∑' k:{k:ℕ // k≤s}, qlow^(s-k.1) := by
    calc
      _=∑' k:ℕ,A*(if k≤s then qlow^(s-k) else 0) := by congr 1; funext k; simp [low]
      _=A*∑' k:ℕ,if k≤s then qlow^(s-k) else 0:=ENNReal.tsum_mul_left
      _=A*∑' k:{k:ℕ // k≤s},qlow^(s-k.1):=by
        congr 1
        have heq:(fun k:ℕ=>if k≤s then qlow^(s-k) else 0)=
          (Set.Iic s).indicator (fun k=>qlow^(s-k)):=by
          funext k; simp [Set.indicator_apply,Set.mem_Iic]
        rw [heq,←tsum_subtype (Set.Iic s)]
        rfl
  have hinj : Function.Injective (fun k:{k:ℕ // k≤s}=>s-k.1) := by
    intro a b hab
    apply Subtype.ext
    have hab' : s-a.1 = s-b.1 := by simpa using hab
    have ha : (s-a.1)+a.1=s := Nat.sub_add_cancel a.2
    have hb : (s-b.1)+b.1=s := Nat.sub_add_cancel b.2
    rw [hab'] at ha
    exact Nat.add_left_cancel (ha.trans hb.symm)
  have hlow_bound : (∑' k:ℕ,low k)≤A*(1-qlow)⁻¹ := by
    rw [hlow_id]
    calc
      A*∑' k:{k:ℕ // k≤s},qlow^(s-k.1)≤A*∑'m:ℕ,qlow^m:=by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun m=>qlow^m)
      _=A*(1-qlow)⁻¹:=by rw [ENNReal.tsum_geometric]
  have hhigh_id : (∑' k:ℕ,high k)=B*∑' k:{k:ℕ // s<k},qhigh^(k.1-s) := by
    calc
      _=∑' k:ℕ,B*(if s<k then qhigh^(k-s) else 0):=by congr 1; funext k; simp [high]
      _=B*∑' k:ℕ,if s<k then qhigh^(k-s) else 0:=ENNReal.tsum_mul_left
      _=B*∑' k:{k:ℕ // s<k},qhigh^(k.1-s):=by
        congr 1
        have heq:(fun k:ℕ=>if s<k then qhigh^(k-s) else 0)=
          (Set.Ioi s).indicator (fun k=>qhigh^(k-s)):=by
          funext k; simp [Set.indicator_apply,Set.mem_Ioi]
        rw [heq,←tsum_subtype (Set.Ioi s)]
        rfl
  let e : {k:ℕ // s<k}→ℕ := fun k=>k.1-s-1
  have heinj:Function.Injective e:=by intro a b h; apply Subtype.ext; dsimp [e] at h; omega
  have hhigh_bound:(∑'k:ℕ,high k)≤B*(qhigh*(1-qhigh)⁻¹):=by
    rw [hhigh_id]
    have hexp(k:{k:ℕ // s<k}):k.1-s=e k+1:=by dsimp [e]; omega
    calc
      B*∑'k:{k:ℕ // s<k},qhigh^(k.1-s)=B*∑'k:{k:ℕ // s<k},qhigh^(e k+1):=by congr 2; funext k; rw [hexp]
      _≤B*∑'m:ℕ,qhigh^(m+1):=by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective heinj (fun m=>qhigh^(m+1))
      _=B*(qhigh*(1-qhigh)⁻¹):=by rw [ENNReal.tsum_geometric_add_one]
  calc
    _≤(∑'k:ℕ,low k)+(∑'k:ℕ,high k):=by simpa [ENNReal.tsum_add] using hsum
    _≤A*(1-qlow)⁻¹+B*(qhigh*(1-qhigh)⁻¹):=add_le_add hlow_bound hhigh_bound

/-- Pointwise low-frequency source estimate, in real form. -/
theorem source_low_real_bound {r C : ℝ} {K s k : ℕ}
    (hr : 0 ≤ r) (hk : k ≤ s) :
    (2 : ℝ) ^ (2*r*((k:ℝ)-(s:ℝ))) * scalarVarianceEnvelope K C s k ≤
      5 * (1/2:ℝ)^(s-k) := by
  have hpow : (2:ℝ)^(2*r*((k:ℝ)-(s:ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hcast : (k:ℝ) ≤ (s:ℝ) := by exact_mod_cast hk
    nlinarith
  simp only [scalarVarianceEnvelope, if_pos hk]
  have hratio : (2:ℝ)^k/(2:ℝ)^s = (1/2:ℝ)^(s-k) := by
    have heq : s = k + (s-k) := (Nat.add_sub_of_le hk).symm
    rw [heq, pow_add]
    field_simp
    simp [one_div, inv_pow]
  rw [hratio]
  calc
    _ ≤ 1 * (5 * (1/2:ℝ)^(s-k)) := by
      apply mul_le_mul_of_nonneg_right hpow
      positivity
    _ = _ := by ring

/-- Pointwise high-frequency source estimate. -/
theorem source_high_real_bound {r C : ℝ} {K s k : ℕ}
    (hK : 1 ≤ K) (hk : s < k) :
    (2 : ℝ) ^ (2*r*((k:ℝ)-(s:ℝ))) * scalarVarianceEnvelope K C s k ≤
      (C^2 * (2:ℝ)^(2*(K:ℝ)+3)) *
        ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s) := by
  have hb := scalar_high_real_bound (C := C) (r := r) hK hk
  have hscale :
      (2:ℝ)^(2*r*((k:ℝ)-(s:ℝ))) * scalarVarianceEnvelope K C s k =
        ((2:ℝ)^(2*r*(k:ℝ))*scalarVarianceEnvelope K C s k) /
          (2:ℝ)^(2*r*(s:ℝ)) := by
    rw [show 2*r*((k:ℝ)-(s:ℝ)) = 2*r*(k:ℝ) - 2*r*(s:ℝ) by ring,
      Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    ring
  rw [hscale]
  calc
    _ ≤ ((C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s)) /
          (2:ℝ)^(2*r*(s:ℝ)) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by
      rw [show 2*(K:ℝ)+3+2*r*(s:ℝ) =
          (2*(K:ℝ)+3) + 2*r*(s:ℝ) by ring,
        Real.rpow_add (by norm_num : (0:ℝ)<2)]
      field_simp

/-- A pointwise low-source bound in the normalized coordinates. -/
theorem sourceNormalizedVariance_low_bound {r C : ℝ} {K s k : ℕ}
    (hr : 0 ≤ r) (hk : k ≤ s) :
    sourceNormalizedVariance r K C s k ≤
      ENNReal.ofReal 5 * (1/2:ℝ≥0∞)^(s-k) := by
  have hreal := source_low_real_bound (C:=C) (K:=K) hr hk
  have he := ENNReal.ofReal_le_ofReal hreal
  have hfac : ENNReal.ofReal (5*(1/2:ℝ)^(s-k)) =
      ENNReal.ofReal 5 * (1/2:ℝ≥0∞)^(s-k) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
    simp [one_div]
  rw [← hfac]
  exact he

/-- A pointwise high-source bound in the normalized coordinates. -/
theorem sourceNormalizedVariance_high_bound {r C : ℝ} {K s k : ℕ}
    (hK : 1 ≤ K) (hk : s < k) :
    sourceNormalizedVariance r K C s k ≤
      ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)) *
        (ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(k-s) := by
  have hreal := source_high_real_bound (C:=C) (r:=r) (K:=K) hK hk
  have he := ENNReal.ofReal_le_ofReal hreal
  have hfac : ENNReal.ofReal ((C^2*(2:ℝ)^(2*(K:ℝ)+3))*
      ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s)) =
      ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)) *
        (ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(k-s) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [← hfac]
  exact he

private theorem ennreal_pow_rpow_comm (x : ℝ≥0∞) (m : ℕ) (u : ℝ) :
    (x ^ m) ^ u = (x ^ u) ^ m := by
  calc
    (x ^ m) ^ u = x ^ ((m : ℝ) * u) := (ENNReal.rpow_natCast_mul x m u).symm
    _ = x ^ (u * m) := by congr 1; ring
    _ = (x ^ u) ^ m := ENNReal.rpow_mul_natCast x u m

/-- Powered source-coordinate scalar summation. Its two geometric ratios are
raised to the same power `u`, so every positive `u≤1` remains summable. -/
theorem sourceNormalizedVariance_rpow_tsum_le {r C : ℝ} {K s : ℕ} {u : ℝ}
    (hK : 1 ≤ K) (hr : 0 ≤ r) (hgap : 2*r < 2*(K:ℝ)-1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, (sourceNormalizedVariance r K C s k)^u) ≤
      (ENNReal.ofReal 5)^u * (1-(1/2:ℝ≥0∞)^u)⁻¹ +
        (ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)))^u *
          (((ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^u) *
            (1-(ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^u)⁻¹) := by
  let qR : ℝ := (2:ℝ)^(2*r-(2*(K:ℝ)-1))
  let q0 : ℝ≥0∞ := ENNReal.ofReal qR
  let qlow : ℝ≥0∞ := (1/2:ℝ≥0∞)^u
  let qhigh : ℝ≥0∞ := q0^u
  let A : ℝ≥0∞ := (ENNReal.ofReal 5)^u
  let B : ℝ≥0∞ := (ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)))^u
  have hqRlt : qR < 1 := by
    dsimp [qR]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hq0lt : q0 < 1 := by
    dsimp [q0]
    rw [show (1:ℝ≥0∞)=ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1) |>.2 hqRlt
  have hhighlt : qhigh < 1 := by
    dsimp [qhigh]
    exact ENNReal.rpow_lt_one hq0lt hu0
  have hlowlt : qlow < 1 := by
    dsimp [qlow]
    exact ENNReal.rpow_lt_one (by norm_num : (1/2:ℝ≥0∞)<1) hu0
  have hlow : ∀ k, k ≤ s → (sourceNormalizedVariance r K C s k)^u ≤
      A * qlow^(s-k) := by
    intro k hk
    have hb := sourceNormalizedVariance_low_bound (C:=C) (K:=K) hr hk
    have hp := ENNReal.rpow_le_rpow hb hu0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hu0.le, ennreal_pow_rpow_comm] at hp
    simpa [A, qlow] using hp
  have hhigh : ∀ k, s < k → (sourceNormalizedVariance r K C s k)^u ≤
      B * qhigh^(k-s) := by
    intro k hk
    have hb := sourceNormalizedVariance_high_bound (C:=C) (r:=r) (K:=K) hK hk
    have hp := ENNReal.rpow_le_rpow hb hu0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hu0.le, ennreal_pow_rpow_comm] at hp
    simpa [B, qhigh, q0, qR] using hp
  have hsplit := forwardTsum_le_of_pointwise_split s qlow qhigh A B hlowlt hhighlt
    (fun k => (sourceNormalizedVariance r K C s k)^u) hlow hhigh
  simpa [A, qlow, B, qhigh, q0, qR] using hsplit

/-- Uniform source-coordinate scalar sum. The budget is the exact same
constant as the target-coordinate l1 series. -/
theorem sourceNormalizedVariance_tsum_le {r C : ℝ} {K k : ℕ}
    (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) :
    (∑' s : ℕ, sourceNormalizedVariance r K C s k) ≤
      ENNReal.ofReal (scalarLayerBudget C r K) := by
  let qR : ℝ := (2:ℝ)^(2*r-(2*(K:ℝ)-1))
  let q : ℝ≥0∞ := ENNReal.ofReal qR
  let A : ℝ≥0∞ := ENNReal.ofReal 5
  let B : ℝ≥0∞ := ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3))
  have hqRlt : qR < 1 := by
    dsimp [qR]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hqRpos : 0 < qR := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [show (1:ℝ≥0∞)=ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1) |>.2 hqRlt
  have hlow : ∀ s, k ≤ s → sourceNormalizedVariance r K C s k ≤
      A*(1/2:ℝ≥0∞)^(s-k) := by
    intro s hs
    have hreal := source_low_real_bound (C:=C) (K:=K) hr hs
    have he := ENNReal.ofReal_le_ofReal hreal
    have hfac : ENNReal.ofReal (5*(1/2:ℝ)^(s-k)) =
        A*(1/2:ℝ≥0∞)^(s-k) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num)]
      simp [A, one_div]
    rw [← hfac]
    exact he
  have hhigh : ∀ s, s < k → sourceNormalizedVariance r K C s k ≤
      B*q^(k-s) := by
    intro s hs
    have hreal := source_high_real_bound (C:=C) (r:=r) (K:=K) hK hs
    have he := ENNReal.ofReal_le_ofReal hreal
    have hfac : ENNReal.ofReal ((C^2*(2:ℝ)^(2*(K:ℝ)+3))*qR^(k-s)) =
        B*q^(k-s) := by
      dsimp [B,q]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    rw [← hfac]
    exact he
  have hsplit0 := reverseTsum_le_of_pointwise_split k (1/2:ℝ≥0∞) q A B (by norm_num) hq1
    (sourceNormalizedVariance r K C · k) hlow hhigh
  have hsplit : (∑' s : ℕ, sourceNormalizedVariance r K C s k) ≤
      A*2+B*(q*(1-q)⁻¹) := by
    simpa using hsplit0
  have hratio : q*(1-q)⁻¹ = ENNReal.ofReal (scalarTailRatio r K) := by
    change ENNReal.ofReal qR * (1-ENNReal.ofReal qR)⁻¹ =
      ENNReal.ofReal (qR/(1-qR))
    have hsub : (1:ℝ≥0∞)-ENNReal.ofReal qR = ENNReal.ofReal (1-qR) := by
      rw [show (1:ℝ≥0∞)=ENNReal.ofReal 1 by norm_num,
        ← ENNReal.ofReal_sub 1 hqRpos.le]
    rw [hsub, ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hqRlt),
      ← ENNReal.ofReal_mul hqRpos.le]
    simp [div_eq_mul_inv]
  have hlowSum : A*2 = ENNReal.ofReal 10 := by
    dsimp [A]
    norm_num [ENNReal.ofReal_mul]
  have hhighSum : B*(q*(1-q)⁻¹) =
      ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)*scalarTailRatio r K) := by
    rw [hratio]
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ C^2*(2:ℝ)^(2*(K:ℝ)+3))]
  have htail_nonneg : 0 ≤ scalarTailRatio r K := by
    unfold scalarTailRatio
    apply div_nonneg
    · positivity
    · have hden : 0 < 1 - (2:ℝ) ^
          (2*r-(2*(K:ℝ)-1)) := by
        apply sub_pos.mpr
        dsimp [qR] at hqRlt ⊢
        exact hqRlt
      exact hden.le
  have hbudget : A*2+B*(q*(1-q)⁻¹) = ENNReal.ofReal (scalarLayerBudget C r K) := by
    rw [hlowSum, hhighSum]
    rw [← ENNReal.ofReal_add (by norm_num) (by positivity [htail_nonneg])]
    rfl
  exact hsplit.trans_eq hbudget

/-- A fixed source shape factors its target-weighted variance into the exact
grade dilation and a product of source-normalized coordinate terms. -/
theorem shape_targetWeighted_eq_sourceNormalized
    (d n K : ℕ) (C r : ℝ) (s : Shape d n) (t : Fin d → ℕ) :
    (∏ i : Fin d, scalarWeightedVariance r K C (s.1 i) (t i)) =
      ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) *
        ∏ i : Fin d, sourceNormalizedVariance r K C (s.1 i) (t i) := by
  have hgrade : (∑ i : Fin d, (s.1 i : ℝ)) = (n : ℝ) := by
    have hh := (Finset.mem_finsuppAntidiag'.mp s.2).1
    have hh' : (∑ i : Fin d, s.1 i) = n := by
      simpa [Finsupp.sum_fintype] using hh
    exact_mod_cast hh'
  have htargetPow : (∏ i : Fin d, (2:ℝ)^(2*r*(t i:ℝ))) =
      (2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)) := by
    calc
      _ = (2:ℝ)^(∑ i : Fin d, 2*r*(t i:ℝ)) := by
        symm
        exact Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)
          (fun i : Fin d => 2*r*(t i:ℝ)) Finset.univ
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
  have hsourcePow :
      (∏ i : Fin d, (2:ℝ)^(2*r*((t i:ℝ)-(s.1 i:ℝ)))) =
        (2:ℝ)^(2*r*((∑ i : Fin d, (t i:ℝ))-(n:ℝ))) := by
    calc
      _ = (2:ℝ)^(∑ i : Fin d,
          2*r*((t i:ℝ)-(s.1 i:ℝ))) := by
        symm
        exact Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)
          (fun i : Fin d => 2*r*((t i:ℝ)-(s.1 i:ℝ))) Finset.univ
      _ = _ := by
        congr 1
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hgrade]
  have hreal :
      (∏ i : Fin d, ((2:ℝ)^(2*r*(t i:ℝ)) *
        scalarVarianceEnvelope K C (s.1 i) (t i))) =
        (2:ℝ)^(2*r*(n:ℝ)) *
          ∏ i : Fin d, ((2:ℝ)^(2*r*((t i:ℝ)-(s.1 i:ℝ))) *
            scalarVarianceEnvelope K C (s.1 i) (t i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      htargetPow, hsourcePow]
    have hpow : (2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)) =
        (2:ℝ)^(2*r*(n:ℝ)) *
          (2:ℝ)^(2*r*((∑ i : Fin d, (t i:ℝ))-(n:ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    rw [hpow]
    ring
  have htarget :
      (∏ i : Fin d, scalarWeightedVariance r K C (s.1 i) (t i)) =
        ENNReal.ofReal (∏ i : Fin d,
          ((2:ℝ)^(2*r*(t i:ℝ))*scalarVarianceEnvelope K C (s.1 i) (t i))) := by
    unfold scalarWeightedVariance
    exact (ENNReal.ofReal_prod_of_nonneg (fun i hi => by
      apply mul_nonneg
      · positivity
      · unfold scalarVarianceEnvelope
        split_ifs <;> positivity)).symm
  have hsource :
      (∏ i : Fin d, sourceNormalizedVariance r K C (s.1 i) (t i)) =
        ENNReal.ofReal (∏ i : Fin d,
          ((2:ℝ)^(2*r*((t i:ℝ)-(s.1 i:ℝ))) *
            scalarVarianceEnvelope K C (s.1 i) (t i))) := by
    unfold sourceNormalizedVariance
    exact (ENNReal.ofReal_prod_of_nonneg (fun i hi => by
      apply mul_nonneg
      · positivity
      · unfold scalarVarianceEnvelope
        split_ifs <;> positivity)).symm
  rw [htarget, hreal]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [← hsource]

/-- Uniform pointwise bound for the full native layer's target-weighted
variance. It sums over all possible source depths coordinatewise, rather than
paying the grade's shape count. -/
theorem nativeLayerWeightedVarianceEnvelope_uniform_le
    (d n K : ℕ) (C r : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (t : Fin d → ℕ) :
    ENNReal.ofReal ((2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)) *
      LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t) ≤
      ENNReal.ofReal (scalarLayerBudget C r K ^ d * (2:ℝ)^(2*r*(n:ℝ))) := by
  classical
  rw [← nativeLayerWeightedEnvelope_eq d n K C r t]
  let f : Fin d → ℕ → ℝ≥0∞ := fun i s => sourceNormalizedVariance r K C s (t i)
  have hsourceShape :
      (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) ≤
        ∏ i : Fin d, ∑' s : ℕ, f i s := by
    have hsum : (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) =
        ∑' a : Shape d n, ∏ i : Fin d, f i (a.1 i) := by
      symm
      exact tsum_fintype (L := .unconditional _) _
    rw [hsum]
    calc
      _ ≤ ∑' s : Fin d → ℕ, ∏ i : Fin d, f i (s i) := by
        let e : Shape d n → (Fin d → ℕ) := fun a i => a.1 i
        have he : Function.Injective e := by
          intro a b h
          apply Subtype.ext
          apply Finsupp.ext
          intro i
          exact congrFun h i
        exact ENNReal.tsum_comp_le_tsum_of_injective he
          (fun s => ∏ i : Fin d, f i (s i))
      _ = ∏ i : Fin d, ∑' s : ℕ, f i s := tsum_pi_prod d f
  have hcoord : ∀ i : Fin d,
      (∑' s : ℕ, f i s) ≤ ENNReal.ofReal (scalarLayerBudget C r K) := by
    intro i
    exact sourceNormalizedVariance_tsum_le hK hr hgap
  have hbudgetnonneg : 0 ≤ scalarLayerBudget C r K := by
    unfold scalarLayerBudget scalarTailRatio
    have hexp : 2*r-(2*(K:ℝ)-1)<0 := by linarith
    have hq : (2:ℝ)^(2*r-(2*(K:ℝ)-1))<1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
    have hden : 0 < 1-(2:ℝ)^(2*r-(2*(K:ℝ)-1)) := sub_pos.mpr hq
    positivity
  have hprod :
      (∏ i : Fin d, ∑' s : ℕ, f i s) ≤
        ENNReal.ofReal (scalarLayerBudget C r K ^ d) := by
    calc
      _ ≤ ∏ i : Fin d, ENNReal.ofReal (scalarLayerBudget C r K) :=
        Finset.prod_le_prod (fun i _ => hcoord i)
      _ = ENNReal.ofReal (scalarLayerBudget C r K ^ d) := by
        rw [← ENNReal.ofReal_prod_of_nonneg]
        · simp
        · intro i hi
          exact hbudgetnonneg
  have hshape := hsourceShape.trans hprod
  have hfinal :
      ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) *
        (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) ≤
      ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) * ENNReal.ofReal (scalarLayerBudget C r K ^ d) :=
    mul_le_mul_of_nonneg_left hshape (by positivity)
  have hshapeEq :
      (∑ a : Shape d n, ∏ i : Fin d,
        scalarWeightedVariance r K C (a.1 i) (t i)) =
      ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) *
        (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) := by
    calc
      _ = ∑ a : Shape d n,
          ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) *
            ∏ i : Fin d, f i (a.1 i) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact shape_targetWeighted_eq_sourceNormalized d n K C r a t
      _ = _ := by
          rw [Finset.mul_sum]
  calc
    _ = ∑ a : Shape d n, ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i) := rfl
    _ = ENNReal.ofReal ((2:ℝ)^(2*r*(n:ℝ))) *
          (∑ a : Shape d n, ∏ i : Fin d, f i (a.1 i)) := hshapeEq
    _ ≤ _ := hfinal
    _ = ENNReal.ofReal (scalarLayerBudget C r K ^ d * (2:ℝ)^(2*r*(n:ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- For every `theta ≥ 2`, the actual native layer has a summable weighted
`theta/2`-power variance envelope. The proof combines the grade-summed l1
bound with the source-uniform pointwise supremum, preserving the exact
weak-composition factor `S_n`. -/
theorem nativeLayerVarianceEnvelope_theta_tsum_le_of_two_le
    (d n K : ℕ) (C r theta : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (htheta : 2 ≤ theta) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
        (LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t)^(theta/2))) ≤
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal
          ((scalarLayerBudget C r K ^ d * (2:ℝ)^(2*r*(n:ℝ)))^(theta/2)) := by
  let M : ℝ := scalarLayerBudget C r K ^ d * (2:ℝ)^(2*r*(n:ℝ))
  let value : (Fin d → ℕ) → ℝ := fun t =>
    (2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)) *
      LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t
  let u : ℝ := theta/2
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hMpos : 0 < M := by
    dsimp [M]
    have hb : 0 < scalarLayerBudget C r K := by
      unfold scalarLayerBudget scalarTailRatio
      have hexp : 2*r-(2*(K:ℝ)-1)<0 := by linarith
      have hq : (2:ℝ)^(2*r-(2*(K:ℝ)-1))<1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
      have hden : 0 < 1-(2:ℝ)^(2*r-(2*(K:ℝ)-1)) := sub_pos.mpr hq
      positivity
    positivity
  have hvalue_nonneg (t : Fin d → ℕ) : 0 ≤ value t := by
    dsimp [value]
    apply mul_nonneg
    · positivity
    · unfold LayerBlockVariance.nativeLayerVarianceEnvelope
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.prod_nonneg
      intro i hi
      unfold scalarVarianceEnvelope
      split_ifs <;> positivity
  have hvalue_le (t : Fin d → ℕ) : value t ≤ M := by
    have h := nativeLayerWeightedVarianceEnvelope_uniform_le
      d n K C r hK hr hgap t
    have hMnonneg : 0 ≤ M := hMpos.le
    exact (ENNReal.ofReal_le_ofReal_iff hMnonneg).mp (by simpa [M, value] using h)
  have hpow (t : Fin d → ℕ) : value t ^ u ≤ M ^ (u-1) * value t := by
    by_cases hz : value t = 0
    · rw [hz]
      simp [Real.zero_rpow (ne_of_gt hu0)]
    · have hvpos : 0 < value t := lt_of_le_of_ne (hvalue_nonneg t) (Ne.symm hz)
      have hmono : value t ^ (u-1) ≤ M ^ (u-1) :=
        Real.rpow_le_rpow (hvalue_nonneg t) (hvalue_le t) (by linarith [hu])
      have heq : value t ^ u = value t ^ (u-1) * value t := by
        calc
          value t ^ u = value t ^ ((u-1)+1) := by congr 1 <;> ring
          _ = value t ^ (u-1) * value t ^ (1:ℝ) := Real.rpow_add hvpos _ _
          _ = value t ^ (u-1) * value t := by rw [Real.rpow_one]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hmono (hvalue_nonneg t)
  have hterm (t : Fin d → ℕ) :
      ENNReal.ofReal (value t ^ u) ≤
        ENNReal.ofReal (M^(u-1)) * ENNReal.ofReal (value t) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)]
    exact ENNReal.ofReal_le_ofReal (hpow t)
  have hsum := ENNReal.tsum_le_tsum hterm
  have hl1 := nativeLayerVarianceEnvelope_weighted_tsum_le
    d n K C r hK hr hgap
  have hsum_bound :
      (∑' t : Fin d → ℕ, ENNReal.ofReal (value t ^ u)) ≤
        ENNReal.ofReal (M^(u-1)) *
          ((Fintype.card (Shape d n) : ℝ≥0∞) * ENNReal.ofReal M) := by
    calc
      _ ≤ ∑' t : Fin d → ℕ,
          ENNReal.ofReal (M^(u-1)) * ENNReal.ofReal (value t) := hsum
      _ = ENNReal.ofReal (M^(u-1)) *
          ∑' t : Fin d → ℕ, ENNReal.ofReal (value t) := ENNReal.tsum_mul_left
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left (by simpa [M, value] using hl1)
          (by positivity)
  have hMpow : ENNReal.ofReal (M^(u-1)) * ENNReal.ofReal M =
      ENNReal.ofReal (M^u) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)]
    congr 1
    calc
      M ^ (u-1) * M = M ^ (u-1) * M ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = M ^ ((u-1)+1) := (Real.rpow_add hMpos _ _).symm
      _ = M ^ u := by congr 1 <;> ring
  have htarget (t : Fin d → ℕ) :
      ENNReal.ofReal (value t ^ u) =
        ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
          (LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t)^u) := by
    congr 1
    dsimp [value]
    have hvar : 0 ≤ LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t := by
      unfold LayerBlockVariance.nativeLayerVarianceEnvelope
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.prod_nonneg
      intro i hi
      unfold scalarVarianceEnvelope
      split_ifs <;> positivity
    rw [Real.mul_rpow (by positivity) hvar]
    have hpow : ((2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)))^u =
        (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) := by
      calc
        _ = (2:ℝ)^((2*r*∑ i : Fin d, (t i:ℝ))*u) :=
          (Real.rpow_mul (by positivity : (0:ℝ)≤2) _ _).symm
        _ = (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) := by congr 1; dsimp [u]; ring
    rw [hpow]
  calc
    _ = ∑' t : Fin d → ℕ, ENNReal.ofReal (value t ^ u) := by
      congr 1
      funext t
      exact (htarget t).symm
    _ ≤ (Fintype.card (Shape d n) : ℝ≥0∞) * ENNReal.ofReal (M^u) := by
      calc
        _ ≤ ENNReal.ofReal (M^(u-1)) *
            ((Fintype.card (Shape d n) : ℝ≥0∞) * ENNReal.ofReal M) := hsum_bound
        _ = (Fintype.card (Shape d n) : ℝ≥0∞) * ENNReal.ofReal (M^u) := by
          calc
            _ = (Fintype.card (Shape d n) : ℝ≥0∞) *
                (ENNReal.ofReal (M^(u-1)) * ENNReal.ofReal M) := by ac_rfl
            _ = (Fintype.card (Shape d n) : ℝ≥0∞) * ENNReal.ofReal (M^u) := by rw [hMpow]
    _ = _ := by simpa [M, u] 

end BrownianSharp.NativeLayerThetaBudget
