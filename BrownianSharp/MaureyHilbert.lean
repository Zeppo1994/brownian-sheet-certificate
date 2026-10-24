import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

/-! Finite-support empirical approximation in a real Hilbert space. -/

noncomputable section
open scoped BigOperators
open InnerProductSpace
open scoped RealInnerProductSpace

namespace BrownianSharp

theorem weighted_centered_sum_eq_zero
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x : H)
    (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i) :
    (∑ i, p i • (x-v i)) = 0 := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, hmean]
  simp

theorem weighted_variance_identity
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x r : H)
    (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i) :
    (∑ i, p i * ‖r + (x-v i)‖ ^ 2) =
      ‖r‖ ^ 2 + ∑ i, p i * ‖x-v i‖ ^ 2 := by
  have hzero := weighted_centered_sum_eq_zero p v x hsum hmean
  have hcross : (∑ i, p i * ⟪r, x-v i⟫) = 0 := by
    calc
      _ = ⟪r, ∑ i, p i • (x-v i)⟫ := by
        simp [inner_sum, inner_smul_right]
      _ = 0 := by rw [hzero]; simp
  simp only [norm_add_sq_real, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ i, p i * ‖r‖ ^ 2) = ‖r‖ ^ 2 by
    rw [← Finset.sum_mul, hsum, one_mul]]
  rw [show (∑ i, p i * (2 * ⟪r, x-v i⟫)) = 0 by
    rw [show (∑ i, p i * (2 * ⟪r, x-v i⟫)) =
      2 * (∑ i, p i * ⟪r, x-v i⟫) by
        calc
          _ = ∑ i, 2 * (p i * ⟪r, x-v i⟫) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.mul_sum]]
    rw [hcross]
    ring]
  ring

theorem weighted_variance_le
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x r : H) (R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i)
    (hbound : ∀ i, ‖v i‖ ≤ R) :
    (∑ i, p i * ‖r + (x-v i)‖ ^ 2) ≤ ‖r‖ ^ 2 + R ^ 2 := by
  rw [weighted_variance_identity p v x r hsum hmean]
  have hsecond : (∑ i, p i * ‖x-v i‖ ^ 2) ≤ R ^ 2 := by
    have hvar : (∑ i, p i * ‖x-v i‖ ^ 2) =
        (∑ i, p i * ‖v i‖ ^ 2) - ‖x‖ ^ 2 := by
      simp only [norm_sub_sq_real, mul_add, mul_sub]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hnormx : (∑ i, p i * ‖x‖ ^ 2) = ‖x‖ ^ 2 := by
        rw [← Finset.sum_mul, hsum, one_mul]
      have hinner : (∑ i, p i * ⟪x, v i⟫) = ‖x‖ ^ 2 := by
        calc
          _ = ⟪x, ∑ i, p i • v i⟫ := by simp [inner_sum, inner_smul_right]
          _ = ‖x‖ ^ 2 := by rw [← hmean, inner_self_eq_norm_sq_to_K]; simp
      have hcross2 : (∑ i, p i * (2 * ⟪x, v i⟫)) = 2 * ‖x‖ ^ 2 := by
        calc
          _ = 2 * (∑ i, p i * ⟪x, v i⟫) := by
            calc
              _ = ∑ i, 2 * (p i * ⟪x, v i⟫) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ = _ := by rw [hinner]
      rw [hnormx, hcross2]
      ring
    rw [hvar]
    have hterms : (∑ i, p i * ‖v i‖ ^ 2) ≤ R ^ 2 := by
      have hR : 0 ≤ R := by
        obtain ⟨j⟩ : Nonempty ι := by
          by_contra hn
          letI : IsEmpty ι := not_nonempty_iff.mp hn
          simp at hsum
        exact le_trans (norm_nonneg _) (hbound j)
      calc
        _ ≤ ∑ i, p i * R ^ 2 := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).2 (hbound i)) (hp i)
        _ = R ^ 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    nlinarith [sq_nonneg ‖x‖]
  linarith

theorem exists_weighted_le_of_average_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p f : ι → ℝ) (B : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (havg : (∑ i, p i * f i) ≤ B) :
    ∃ i, 0 < p i ∧ f i ≤ B := by
  have hpos : ∃ i, 0 < p i := by
    by_contra hn
    have hle : ∀ i, p i ≤ 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, lt_of_not_ge hi⟩
    have hsumle : (∑ i, p i) ≤ ∑ i, (0 : ℝ) :=
      Finset.sum_le_sum fun i hi => hle i
    rw [hsum] at hsumle
    norm_num at hsumle
  by_contra h
  have hbad : ∀ i, 0 < p i → B < f i := by
    intro i hpi
    by_contra hfi
    exact h ⟨i, hpi, le_of_not_gt hfi⟩
  obtain ⟨i, hpi⟩ := hpos
  have hstrict :
      (∑ i, p i * B) < ∑ i, p i * f i := by
    apply Finset.sum_lt_sum
    · intro j hj
      by_cases hpj : p j = 0
      · simp [hpj]
      · have hpjpos : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hpj)
        exact mul_le_mul_of_nonneg_left (le_of_lt (hbad j hpjpos)) (hp j)
    · exact ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (hbad i hpi) hpi⟩
  have : B < ∑ i, p i * f i := by
    calc
      B = ∑ i, p i * B := by rw [← Finset.sum_mul, hsum, one_mul]
      _ < ∑ i, p i * f i := hstrict
  linarith

theorem exists_maurey_step
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x r : H) (R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i)
    (hbound : ∀ i, ‖v i‖ ≤ R) :
    ∃ i, 0 < p i ∧ ‖r + (x-v i)‖ ^ 2 ≤ ‖r‖ ^ 2 + R ^ 2 := by
  apply exists_weighted_le_of_average_le p (fun i => ‖r + (x-v i)‖ ^ 2)
    (‖r‖ ^ 2 + R ^ 2) hp hsum
  exact weighted_variance_le p v x r R hp hsum hmean hbound

theorem exists_maurey_residual_list
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x : H) (R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i)
    (hbound : ∀ i, ‖v i‖ ≤ R) :
    ∀ n : ℕ, ∃ l : List ι, l.length = n ∧
      ‖(n : ℝ) • x - (l.map v).sum‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
  intro n
  induction n with
  | zero =>
      refine ⟨[], rfl, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨l, hlen, hresBound⟩ := ih
      let r : H := (n : ℝ) • x - (l.map v).sum
      obtain ⟨i, hpi, hstep⟩ := exists_maurey_step p v x r R hp hsum hmean hbound
      refine ⟨l ++ [i], ?_, ?_⟩
      · simp [hlen]
      · have hres : ((n+1 : ℕ) : ℝ) • x - ((l ++ [i]).map v).sum =
            r + (x-v i) := by
          simp [r, List.map_append, List.sum_append, Nat.cast_succ, add_smul]
          abel
        rw [hres]
        have hprev : ‖r‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
          simpa [r] using hresBound
        have hcast : ((n+1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
        rw [hcast]
        nlinarith [hstep, hprev]

theorem exists_maurey_average
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ι → ℝ) (v : ι → H) (x : H) (R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmean : x = ∑ i, p i • v i)
    (hbound : ∀ i, ‖v i‖ ≤ R)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ l : List ι, l.length = s ∧
      ‖(s : ℝ)⁻¹ • (l.map v).sum - x‖ ^ 2 ≤ R ^ 2 / (s : ℝ) := by
  obtain ⟨l, hlen, hres⟩ := exists_maurey_residual_list p v x R hp hsum hmean hbound s
  refine ⟨l, hlen, ?_⟩
  let a : ℝ := (s : ℝ)⁻¹
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hs)
  have hsne : (s : ℝ) ≠ 0 := hspos.ne'
  have hresid : (a • (l.map v).sum - x) =
      - (a • ((s : ℝ) • x - (l.map v).sum)) := by
    dsimp [a]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hsne]
    simp only [one_smul]
    abel
  rw [hresid, norm_neg, norm_smul]
  have hinvpos : 0 ≤ a := by dsimp [a]; positivity
  have hres' : ‖(s : ℝ) • x - (l.map v).sum‖ ^ 2 ≤ (s : ℝ) * R ^ 2 := hres
  calc
    (‖a‖ * ‖(s : ℝ) • x - (l.map v).sum‖) ^ 2 ≤
        ‖a‖ ^ 2 * ((s : ℝ) * R ^ 2) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hres' (sq_nonneg ‖a‖)
    _ = R ^ 2 / (s : ℝ) := by
      have habs : ‖a‖ = (s : ℝ)⁻¹ := by simp [a, abs_of_pos hspos]
      rw [habs]
      field_simp

end BrownianSharp

end

noncomputable section
namespace BrownianSharp

def signedDictionaryAtom {ι H : Type*} [NormedAddCommGroup H]
    (coeff : ι → ℝ) (v : ι → H) : Option ι → H
  | none => 0
  | some i => if 0 ≤ coeff i then v i else -v i

def signedDictionaryWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : ι → ℝ) : Option ι → ℝ
  | none => 1 - ∑ i, |coeff i|
  | some i => |coeff i|

theorem signed_dictionary_weight_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : ι → ℝ) :
    (∑ o : Option ι, signedDictionaryWeight coeff o) = 1 := by
  simp [signedDictionaryWeight, Fintype.sum_option]

theorem signed_dictionary_weight_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : ι → ℝ)
    (hcoeff : ∑ i, |coeff i| ≤ 1) :
    ∀ o : Option ι, 0 ≤ signedDictionaryWeight coeff o := by
  intro o
  cases o with
  | none => simp [signedDictionaryWeight]; linarith
  | some i => simp [signedDictionaryWeight]

theorem signed_dictionary_mean
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (coeff : ι → ℝ) (v : ι → H) :
    (∑ o : Option ι, signedDictionaryWeight coeff o • signedDictionaryAtom coeff v o) =
      ∑ i, coeff i • v i := by
  simp only [Fintype.sum_option, signedDictionaryWeight, signedDictionaryAtom,
    smul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 ≤ coeff i
  · simp [h, abs_of_nonneg h]
  · have hn : coeff i < 0 := lt_of_not_ge h
    simp [h, abs_of_neg hn, neg_smul]

theorem exists_signed_dictionary_average
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (coeff : ι → ℝ) (v : ι → H) (x : H) (R : ℝ)
    (hcoeff : ∑ i, |coeff i| ≤ 1)
    (hx : x = ∑ i, coeff i • v i)
    (hR : 0 ≤ R) (hbound : ∀ i, ‖v i‖ ≤ R)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ l : List (Option ι), l.length = s ∧
      ‖(s : ℝ)⁻¹ • (l.map (signedDictionaryAtom coeff v)).sum - x‖ ^ 2 ≤
        R ^ 2 / (s : ℝ) := by
  have hp : ∀ o : Option ι, 0 ≤ signedDictionaryWeight coeff o :=
    signed_dictionary_weight_nonneg coeff hcoeff
  have hsum := signed_dictionary_weight_sum coeff
  have hmean : x = ∑ o : Option ι,
      signedDictionaryWeight coeff o • signedDictionaryAtom coeff v o := by
    rw [signed_dictionary_mean]
    exact hx
  have hb : ∀ o : Option ι, ‖signedDictionaryAtom coeff v o‖ ≤ R := by
    intro o
    cases o with
    | none => simp [signedDictionaryAtom]; exact hR
    | some i =>
      by_cases h : 0 ≤ coeff i <;> simp [signedDictionaryAtom, h, norm_neg, hbound i]
  exact exists_maurey_average (signedDictionaryWeight coeff)
    (signedDictionaryAtom coeff v) x R hp hsum hmean hb s hs


def jointDictionaryAtom {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (v : ι → H) (i : ι) : WithLp 2 (H × E) :=
  WithLp.toLp 2 (v i, A (v i))

theorem exists_signed_dictionary_joint_average
    {ι H E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (coeff : ι → ℝ) (v : ι → H) (x : H) (R : ℝ)
    (hcoeff : ∑ i, |coeff i| ≤ 1)
    (hx : x = ∑ i, coeff i • v i)
    (hAx : A x = 0)
    (hR : 0 ≤ R) (hbound : ∀ i, ‖v i‖ ≤ R)
    (hAbound : ∀ i, ‖A (v i)‖ ≤ 2 * R)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ l : List (Option ι), l.length = s ∧
      ‖(s : ℝ)⁻¹ • (l.map (fun o => signedDictionaryAtom coeff (jointDictionaryAtom A v) o)).sum -
          WithLp.toLp 2 (x, (0 : E))‖ ^ 2 ≤ 5 * R ^ 2 / (s : ℝ) := by
  let W := WithLp 2 (H × E)
  let w : ι → W := jointDictionaryAtom A v
  have hpairSum : (∑ i, coeff i • w i).ofLp =
      (∑ i, coeff i • v i, ∑ i, coeff i • A (v i)) := by
    change (WithLp.linearEquiv 2 ℝ (H × E)) (∑ i, coeff i • w i) = _
    rw [map_sum]
    simp only [map_smul]
    apply Prod.ext <;> simp [w, jointDictionaryAtom, Prod.fst_sum, Prod.snd_sum]
  have hsecond : (∑ i, coeff i • A (v i)) = 0 := by
    calc
      _ = A (∑ i, coeff i • v i) := by simp
      _ = A x := by rw [← hx]
      _ = 0 := hAx
  have hmean : WithLp.toLp 2 (x, (0 : E)) =
      ∑ i, coeff i • w i := by
    rw [WithLp.ext_iff]
    rw [WithLp.ofLp_toLp, hpairSum]
    exact Prod.ext hx hsecond.symm
  have hboundW : ∀ i, ‖w i‖ ≤ Real.sqrt 5 * R := by
    intro i
    have h1 : ‖v i‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).2 (hbound i)
    have h2 : ‖A (v i)‖ ^ 2 ≤ (2 * R) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR)).2 (hAbound i)
    have hnorm : ‖w i‖ ^ 2 = ‖v i‖ ^ 2 + ‖A (v i)‖ ^ 2 := by
      change ‖WithLp.toLp 2 (v i, A (v i))‖ ^ 2 = _
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp
    have hsqrt : 0 ≤ Real.sqrt 5 * R := mul_nonneg (Real.sqrt_nonneg _) hR
    apply (sq_le_sq₀ (norm_nonneg _) hsqrt).1
    rw [hnorm]
    nlinarith [sq_nonneg (‖v i‖), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  have hmean' : WithLp.toLp 2 (x, (0 : E)) = ∑ i, coeff i • w i := hmean
  obtain ⟨l, hl, hle⟩ := exists_signed_dictionary_average coeff w
      (WithLp.toLp 2 (x, (0 : E))) (Real.sqrt 5 * R)
      hcoeff hmean' (mul_nonneg (Real.sqrt_nonneg _) hR) hboundW s hs
  refine ⟨l, hl, ?_⟩
  have hscale : (Real.sqrt 5 * R) ^ 2 = 5 * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  rw [hscale] at hle
  exact hle


private theorem signed_joint_atom_ofLp
    {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (coeff : ι → ℝ) (v : ι → H) (o : Option ι) :
    (signedDictionaryAtom coeff (jointDictionaryAtom A v) o).ofLp =
      (signedDictionaryAtom coeff v o, A (signedDictionaryAtom coeff v o)) := by
  cases o with
  | none =>
      simp only [signedDictionaryAtom]
      change (WithLp.linearEquiv 2 ℝ (H × E)) (0 : WithLp 2 (H × E)) = _
      simp
      exact Prod.ext rfl rfl
  | some i =>
      by_cases h : 0 ≤ coeff i <;>
        simp [signedDictionaryAtom, jointDictionaryAtom, h]

private theorem list_signed_joint_atom_ofLp
    {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (coeff : ι → ℝ) (v : ι → H) (l : List (Option ι)) :
    ((l.map (signedDictionaryAtom coeff (jointDictionaryAtom A v))).sum).ofLp =
      ((l.map (signedDictionaryAtom coeff v)).sum,
        (l.map (fun o => A (signedDictionaryAtom coeff v o))).sum) := by
  induction l with
  | nil =>
      change (0 : H × E) = (0, 0)
      exact Prod.ext rfl rfl
  | cons o l ih =>
      simp only [List.map_cons, List.sum_cons]
      change (WithLp.linearEquiv 2 ℝ (H × E))
          (signedDictionaryAtom coeff (jointDictionaryAtom A v) o +
            (l.map (signedDictionaryAtom coeff (jointDictionaryAtom A v))).sum) = _
      rw [map_add]
      change (signedDictionaryAtom coeff (jointDictionaryAtom A v) o).ofLp +
          ((l.map (signedDictionaryAtom coeff (jointDictionaryAtom A v))).sum).ofLp = _
      rw [signed_joint_atom_ofLp, ih]
      rfl

theorem exists_signed_dictionary_joint_image_average
    {ι H E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (coeff : ι → ℝ) (v : ι → H) (x : H) (R : ℝ)
    (hcoeff : ∑ i, |coeff i| ≤ 1)
    (hx : x = ∑ i, coeff i • v i)
    (hAx : A x = 0)
    (hR : 0 ≤ R) (hbound : ∀ i, ‖v i‖ ≤ R)
    (hAbound : ∀ i, ‖A (v i)‖ ≤ 2 * R)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ l : List (Option ι), l.length = s ∧
      let y : H := (s : ℝ)⁻¹ • (l.map (signedDictionaryAtom coeff v)).sum
      ‖y - x‖ ^ 2 + ‖A y‖ ^ 2 ≤ 5 * R ^ 2 / (s : ℝ) := by
  obtain ⟨l, hl, hjoint⟩ := exists_signed_dictionary_joint_average
    A coeff v x R hcoeff hx hAx hR hbound hAbound s hs
  refine ⟨l, hl, ?_⟩
  dsimp
  let y : H := (s : ℝ)⁻¹ • (l.map (signedDictionaryAtom coeff v)).sum
  let z : WithLp 2 (H × E) :=
    (s : ℝ)⁻¹ • (l.map (fun o => signedDictionaryAtom coeff
      (jointDictionaryAtom A v) o)).sum - WithLp.toLp 2 (x, (0 : E))
  have hz : z.ofLp = (y - x, A y) := by
    change (WithLp.linearEquiv 2 ℝ (H × E)) z = _
    simp only [z, map_sub, map_smul]
    have hlpair := list_signed_joint_atom_ofLp A coeff v l
    change (s : ℝ)⁻¹ •
        (WithLp.linearEquiv 2 ℝ (H × E))
          ((l.map (fun o => signedDictionaryAtom coeff (jointDictionaryAtom A v) o)).sum) -
        (WithLp.linearEquiv 2 ℝ (H × E)) (WithLp.toLp 2 (x, (0 : E))) = _
    rw [show (WithLp.linearEquiv 2 ℝ (H × E))
        ((l.map (fun o => signedDictionaryAtom coeff (jointDictionaryAtom A v) o)).sum) =
          ((l.map (signedDictionaryAtom coeff v)).sum,
            (l.map (fun o => A (signedDictionaryAtom coeff v o))).sum) by exact hlpair]
    have hAList : (l.map (fun o => A (signedDictionaryAtom coeff v o))).sum =
        A ((l.map (signedDictionaryAtom coeff v)).sum) := by
      have hfun : (fun o => A (signedDictionaryAtom coeff v o)) =
          (A.toLinearMap.toAddMonoidHom ∘ signedDictionaryAtom coeff v) := by
        funext o
        rfl
      rw [hfun, ← List.map_map]
      exact (map_list_sum A.toLinearMap.toAddMonoidHom
        (l.map (signedDictionaryAtom coeff v))).symm
    simp [y, hAList]
  have hnorm : ‖z‖ ^ 2 = ‖y - x‖ ^ 2 + ‖A y‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖z.ofLp.1‖ ^ 2 + ‖z.ofLp.2‖ ^ 2 = _
    rw [hz]
  rw [← hnorm]
  exact hjoint

end BrownianSharp

end
