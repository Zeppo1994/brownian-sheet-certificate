import BrownianSharp.TheoremDSineSampling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

open scoped BigOperators

namespace HaarQuarter.TheoremD.Fejer

noncomputable def midpointPhase (N k j : ℕ) : ℝ :=
  2 * Real.pi * (k : ℝ) * ((j : ℝ) + 1 / 2) / N

noncomputable def midpointCharacter (N k j : ℕ) : ℂ :=
  Complex.exp ((↑(midpointPhase N k j) : ℂ) * Complex.I)

noncomputable def midpointPhaseShift (k : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((↑(-2 * Real.pi * (k : ℝ) * t) : ℂ) * Complex.I)

noncomputable def shiftedMidpointCharacter (N k j : ℕ) (t : ℝ) : ℂ :=
  midpointPhaseShift k t * midpointCharacter N k j

noncomputable def midpointGridStepPhase (N j : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * N * (((j : ℝ) + 1 / 2) / N - t)) : ℂ) * Complex.I)

/-- Splitting the length-2N geometric sum into two length-N sums introduces
only a unit phase on the translated midpoint grid. -/
theorem shifted_midpoint_character_succ_block (N r j : ℕ) (t : ℝ) :
    shiftedMidpointCharacter N (r + N) j t =
      midpointGridStepPhase N j t * shiftedMidpointCharacter N r j t := by
  simp only [shiftedMidpointCharacter, midpointPhaseShift, midpointCharacter,
    midpointPhase, midpointGridStepPhase]
  rw [show 2 * Real.pi * ((r + N : ℕ) : ℝ) * ((j : ℝ) + 1 / 2) / N =
      2 * Real.pi * (r : ℝ) * ((j : ℝ) + 1 / 2) / N +
        2 * Real.pi * N * (((j : ℝ) + 1 / 2) / N) by
        push_cast
        field_simp
        ]
  rw [show -2 * Real.pi * ((r + N : ℕ) : ℝ) * t =
      (-2 * Real.pi * (r : ℝ) * t) + (-2 * Real.pi * N * t) by
        push_cast
        ring]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem normSq_add_phase_mul_le (a q : ℂ) (hq : ‖q‖ = 1) :
    Complex.normSq (a + q * a) ≤ 4 * Complex.normSq a := by
  have hnorm : ‖a + q * a‖ ≤ 2 * ‖a‖ := by
    calc
      ‖a + q * a‖ ≤ ‖a‖ + ‖q * a‖ := norm_add_le _ _
      _ = 2 * ‖a‖ := by rw [norm_mul, hq]; ring
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hnonneg : 0 ≤ ‖a + q * a‖ := norm_nonneg _
  have hnonnega : 0 ≤ ‖a‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a + q * a‖), sq_nonneg (‖a‖)]

/-- Pointwise, the length-2N Fejer numerator is at most four times the
length-N numerator on the same translated N-point grid. -/
theorem shifted_double_character_sum_normSq_le (N j : ℕ) (t : ℝ) :
    Complex.normSq (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t) ≤
      4 * Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) := by
  have hsplit :
      (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t) =
        (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) +
          midpointGridStepPhase N j t *
            (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) := by
    rw [show 2 * N = N + N by omega, Finset.sum_range_add]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    simpa [Nat.add_comm] using shifted_midpoint_character_succ_block N r j t
  rw [hsplit]
  apply normSq_add_phase_mul_le
  exact Complex.norm_exp_ofReal_mul_I _

/-- Nonzero frequencies below the grid size have zero average on the midpoint
grid. This is the complex root-of-unity orthogonality identity used in the
finite Fejer calculation. -/
theorem midpoint_root_sum_eq_zero (N q : ℕ) (hN : 0 < N)
    (hq : 0 < q) (hqN : q < N) :
    (∑ j ∈ Finset.range N,
      Complex.exp ((↑(midpointPhase N q j) : ℂ) * Complex.I)) = 0 := by
  have hcos := HaarQuarter.TheoremD.SineSampling.midpoint_cos_sum_eq_zero
    N (2 * q) hN (by omega) (by omega)
  have hsinProduct :
      Real.sin (Real.pi * q / N) *
        (∑ j ∈ Finset.range N,
          Real.sin ((2 * Real.pi * q / N) * j + Real.pi * q / N)) = 0 := by
    have h := Real.sin_mul_sum_sin N (2 * Real.pi * q / N) (Real.pi * q / N)
    have hphase : (2 * Real.pi * q / N) / 2 = Real.pi * q / N := by ring
    have hend : ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * q / N) / 2 +
        Real.pi * q / N = Real.pi * q := by
      have hN1 : 1 ≤ N := hN
      rw [Nat.cast_sub hN1]
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring
    have hleft : Real.sin (2 * Real.pi * q / N / 2) =
        Real.sin (Real.pi * q / N) := by rw [hphase]
    have hright₁ : Real.sin ((N : ℝ) * (2 * Real.pi * q / N) / 2) = 0 := by
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hNphase : (N : ℝ) * (2 * Real.pi * q / N) / 2 =
          (q : ℝ) * Real.pi := by field_simp
      rw [hNphase, Real.sin_nat_mul_pi]
    have hright₂ : Real.sin (((N - 1 : ℕ) : ℝ) * (2 * Real.pi * q / N) / 2 +
        Real.pi * q / N) = 0 := by
      rw [hend, show Real.pi * (q : ℝ) = (q : ℝ) * Real.pi by ring,
        Real.sin_nat_mul_pi]
    simp only [hleft, hright₁, hright₂, mul_zero] at h
    simpa [mul_zero] using h
  have hsinNonzero : Real.sin (Real.pi * q / N) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · positivity
    · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < N)]
      have hqR : (q : ℝ) < N := by exact_mod_cast hqN
      nlinarith [Real.pi_pos, hqR]
  have hsin :
      (∑ j ∈ Finset.range N,
        Real.sin ((2 * Real.pi * q / N) * j + Real.pi * q / N)) = 0 :=
    (mul_eq_zero.mp hsinProduct).resolve_left hsinNonzero
  let θ : ℕ → ℝ := fun j => 2 * Real.pi * (q : ℝ) * ((j : ℝ) + 1 / 2) / N
  have htheta (j : ℕ) : θ j =
      (2 * Real.pi * q / N) * j + Real.pi * q / N := by
    dsimp [θ]
    push_cast
    ring
  have hpoint (j : ℕ) :
      (2 * (q : ℝ)) * HaarQuarter.TheoremD.SineSampling.midpointAngle N j = θ j := by
    dsimp [θ, HaarQuarter.TheoremD.SineSampling.midpointAngle]
    push_cast
    ring
  have hcos' : (∑ j ∈ Finset.range N, Real.cos (θ j)) = 0 := by
    convert hcos using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have hcast : ((2 * q : ℕ) : ℝ) = 2 * (q : ℝ) := by norm_num
    rw [hcast]
    exact (hpoint j).symm
  have hsin' : (∑ j ∈ Finset.range N, Real.sin (θ j)) = 0 := by
    convert hsin using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact htheta j
  apply Complex.ext
  · calc
      (∑ j ∈ Finset.range N,
        Complex.exp
          ((↑(2 * Real.pi * (q : ℝ) * ((j : ℝ) + 1 / 2) / N) : ℂ) *
            Complex.I)).re
          = ∑ j ∈ Finset.range N, Real.cos (θ j) := by
              rw [Complex.re_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Complex.exp_ofReal_mul_I_re]
      _ = 0 := hcos'
  · calc
      (∑ j ∈ Finset.range N,
        Complex.exp
          ((↑(2 * Real.pi * (q : ℝ) * ((j : ℝ) + 1 / 2) / N) : ℂ) *
            Complex.I)).im
          = ∑ j ∈ Finset.range N, Real.sin (θ j) := by
              rw [Complex.im_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Complex.exp_ofReal_mul_I_im]
      _ = 0 := hsin'

/-- The corresponding negative-frequency sum vanishes by complex
conjugation. -/
theorem midpoint_root_sum_neg_eq_zero (N q : ℕ) (hN : 0 < N)
    (hq : 0 < q) (hqN : q < N) :
    (∑ j ∈ Finset.range N,
      Complex.exp (-(↑(midpointPhase N q j) * Complex.I))) = 0 := by
  have h := midpoint_root_sum_eq_zero N q hN hq hqN
  have hc := congrArg (starRingEnd ℂ) h
  rw [map_sum, map_zero] at hc
  simpa only [← Complex.exp_conj, map_mul, star_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_mul] using hc

/-- Distinct sampled characters are orthogonal on the midpoint grid; this
form exposes the signed frequency difference needed by the Fejer square. -/
theorem midpoint_root_sum_difference_eq_zero (N r s : ℕ)
    (hN : 0 < N) (hr : r < N) (hs : s < N) (hrs : r ≠ s) :
    (∑ j ∈ Finset.range N,
      Complex.exp
        ((↑(midpointPhase N s j - midpointPhase N r j) : ℂ) * Complex.I)) = 0 := by
  by_cases hrs' : r < s
  · have hq : 0 < s - r := by omega
    have hqN : s - r < N := by omega
    have hphase (j : ℕ) : midpointPhase N s j - midpointPhase N r j =
        midpointPhase N (s - r) j := by
      dsimp [midpointPhase]
      rw [Nat.cast_sub (by omega : r ≤ s)]
      ring
    convert midpoint_root_sum_eq_zero N (s - r) hN hq hqN using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hphase]
  · have hsr : s < r := by omega
    have hq : 0 < r - s := by omega
    have hqN : r - s < N := by omega
    have hphase (j : ℕ) : midpointPhase N s j - midpointPhase N r j =
        -(midpointPhase N (r - s) j) := by
      dsimp [midpointPhase]
      rw [Nat.cast_sub (by omega : s ≤ r)]
      ring
    convert midpoint_root_sum_neg_eq_zero N (r - s) hN hq hqN using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hphase]
    simp only [Complex.ofReal_neg, neg_mul]

/-- The N midpoint characters form an orthogonal family with squared norm N. -/
theorem midpoint_character_inner (N r s : ℕ) (hN : 0 < N)
    (hr : r < N) (hs : s < N) :
    (∑ j ∈ Finset.range N,
      star (midpointCharacter N r j) * midpointCharacter N s j) =
      if r = s then (N : ℂ) else 0 := by
  have hterm (j : ℕ) :
      star (midpointCharacter N r j) * midpointCharacter N s j =
        Complex.exp ((↑(midpointPhase N s j - midpointPhase N r j) : ℂ) *
          Complex.I) := by
    simp only [midpointCharacter]
    change (starRingEnd ℂ)
        (Complex.exp ((↑(midpointPhase N r j) : ℂ) * Complex.I)) *
          Complex.exp ((↑(midpointPhase N s j) : ℂ) * Complex.I) = _
    have hstar (x : ℝ) :
        star (Complex.exp ((↑x : ℂ) * Complex.I)) =
          Complex.exp (-((↑x : ℂ) * Complex.I)) := by
      change (starRingEnd ℂ) (Complex.exp ((↑x : ℂ) * Complex.I)) = _
      rw [← Complex.exp_conj]
      apply congrArg Complex.exp
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [starRingEnd_apply, hstar]
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_sub]
    ring
  by_cases hrs : r = s
  · subst s
    calc
      _ = ∑ j ∈ Finset.range N,
          Complex.exp ((↑(midpointPhase N r j - midpointPhase N r j) : ℂ) *
            Complex.I) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm j
      _ = (N : ℂ) := by simp
    simp
  · rw [if_neg hrs]
    calc
      (∑ j ∈ Finset.range N,
        star (midpointCharacter N r j) * midpointCharacter N s j) =
          ∑ j ∈ Finset.range N,
            Complex.exp ((↑(midpointPhase N s j - midpointPhase N r j) : ℂ) *
              Complex.I) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact hterm j
      _ = 0 := midpoint_root_sum_difference_eq_zero N r s hN hr hs hrs

/-- Character orthogonality persists after an arbitrary common translation
of the sampling grid. -/
theorem shifted_midpoint_character_inner (N r s : ℕ) (t : ℝ) (hN : 0 < N)
    (hr : r < N) (hs : s < N) :
    (∑ j ∈ Finset.range N,
      star (shiftedMidpointCharacter N r j t) *
        shiftedMidpointCharacter N s j t) =
      if r = s then (N : ℂ) else 0 := by
  have hfactor (j : ℕ) :
      star (shiftedMidpointCharacter N r j t) *
        shiftedMidpointCharacter N s j t =
        (star (midpointPhaseShift r t) * midpointPhaseShift s t) *
          (star (midpointCharacter N r j) * midpointCharacter N s j) := by
    simp only [shiftedMidpointCharacter, star_mul]
    ac_rfl
  calc
    _ = (star (midpointPhaseShift r t) * midpointPhaseShift s t) *
        (∑ j ∈ Finset.range N,
          star (midpointCharacter N r j) * midpointCharacter N s j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact hfactor j
    _ = _ := by
          rw [midpoint_character_inner N r s hN hr hs]
          by_cases hrs : r = s
          · subst s
            simp only [if_pos rfl]
            have hstar (x : ℝ) :
                star (Complex.exp ((↑x : ℂ) * Complex.I)) =
                  Complex.exp (-((↑x : ℂ) * Complex.I)) := by
              change (starRingEnd ℂ) (Complex.exp ((↑x : ℂ) * Complex.I)) = _
              rw [← Complex.exp_conj]
              apply congrArg Complex.exp
              rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
              ring
            have hphase : star (midpointPhaseShift r t) * midpointPhaseShift r t = 1 := by
              rw [show midpointPhaseShift r t =
                Complex.exp ((↑(-2 * Real.pi * (r : ℝ) * t) : ℂ) * Complex.I) by rfl]
              rw [hstar, ← Complex.exp_add]
              congr 1
              ring
              simp
            change (star (midpointPhaseShift r t) * midpointPhaseShift r t) *
              (N : ℂ) = (N : ℂ)
            rw [hphase, one_mul]
          · simp [if_neg hrs]

/-- Expand the squared norm of a finite complex character sum into its Gram
matrix. -/
theorem normSq_finset_sum_expand {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (Complex.normSq (∑ i ∈ s, f i) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (f i) * f j := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
  simp only [starRingEnd_apply]

/-- Parseval on the midpoint grid: the squared norm of the length-N Fourier
sum has total discrete mass N². -/
theorem midpoint_character_sum_normSq_total (N : ℕ) (hN : 0 < N) :
    (↑(∑ j ∈ Finset.range N,
      Complex.normSq (∑ r ∈ Finset.range N, midpointCharacter N r j)) : ℂ) =
      (N : ℂ) ^ 2 := by
  calc
    _ = ∑ j ∈ Finset.range N,
        (Complex.normSq (∑ r ∈ Finset.range N, midpointCharacter N r j) : ℂ) := by
          rw [Complex.ofReal_sum]
    _ = ∑ j ∈ Finset.range N, ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          star (midpointCharacter N r j) * midpointCharacter N s j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact normSq_finset_sum_expand (Finset.range N)
            (fun r => midpointCharacter N r j)
    _ = ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N, ∑ j ∈ Finset.range N,
          star (midpointCharacter N r j) * midpointCharacter N s j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          (if r = s then (N : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          exact midpoint_character_inner N r s hN (Finset.mem_range.mp hr)
            (Finset.mem_range.mp hs)
    _ = (N : ℂ) ^ 2 := by
          calc
            _ = ∑ r ∈ Finset.range N, (N : ℂ) := by
              apply Finset.sum_congr rfl
              intro r hr
              have hrlt : r < N := Finset.mem_range.mp hr
              simp [Finset.sum_ite_eq', eq_comm, hrlt]
            _ = (N : ℂ) ^ 2 := by
              rw [Finset.sum_const]
              simp
              ring

/-- The same Parseval mass identity holds uniformly for a translated grid. -/
theorem shifted_midpoint_character_sum_normSq_total (N : ℕ) (t : ℝ)
    (hN : 0 < N) :
    (↑(∑ j ∈ Finset.range N,
      Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t)) : ℂ) =
      (N : ℂ) ^ 2 := by
  calc
    _ = ∑ j ∈ Finset.range N,
        (Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) : ℂ) := by
          rw [Complex.ofReal_sum]
    _ = ∑ j ∈ Finset.range N, ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          star (shiftedMidpointCharacter N r j t) * shiftedMidpointCharacter N s j t := by
          apply Finset.sum_congr rfl
          intro j hj
          exact normSq_finset_sum_expand (Finset.range N)
            (fun r => shiftedMidpointCharacter N r j t)
    _ = ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N, ∑ j ∈ Finset.range N,
          star (shiftedMidpointCharacter N r j t) * shiftedMidpointCharacter N s j t := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
          (if r = s then (N : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          exact shifted_midpoint_character_inner N r s t hN
            (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)
    _ = (N : ℂ) ^ 2 := by
          calc
            _ = ∑ r ∈ Finset.range N, (N : ℂ) := by
              apply Finset.sum_congr rfl
              intro r hr
              have hrlt : r < N := Finset.mem_range.mp hr
              simp [hrlt]
            _ = (N : ℂ) ^ 2 := by
              rw [Finset.sum_const]
              simp
              ring

/-- The normalized length-N Fejer kernel has average one on every translated
midpoint grid. -/
theorem shifted_fejer_average_eq_one (N : ℕ) (t : ℝ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N,
      Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) /
        (N : ℝ)) / N = 1 := by
  have hmass :
      (∑ j ∈ Finset.range N,
        Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t)) =
        (N : ℝ) ^ 2 := by
    exact_mod_cast shifted_midpoint_character_sum_normSq_total N t hN
  rw [← Finset.sum_div, hmass]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- On the same translated N-point grid, the average normalized length-2N
Fejer kernel is at most two. -/
theorem shifted_double_fejer_average_le_two (N : ℕ) (t : ℝ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N,
      Complex.normSq (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t) /
        (2 * N : ℝ)) / N ≤ 2 := by
  have hmassN :
      (∑ j ∈ Finset.range N,
        Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t)) =
        (N : ℝ) ^ 2 := by
    exact_mod_cast shifted_midpoint_character_sum_normSq_total N t hN
  have hsum :
      (∑ j ∈ Finset.range N,
        Complex.normSq (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t)) ≤
        4 * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          4 * Complex.normSq (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) := by
            apply Finset.sum_le_sum
            intro j hj
            exact shifted_double_character_sum_normSq_le N j t
      _ = 4 * (N : ℝ) ^ 2 := by rw [← Finset.mul_sum, hmassN]
  rw [← Finset.sum_div]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (0 : ℝ) < 2 * N := by positivity
  apply (div_le_iff₀ hNpos).2
  apply (div_le_iff₀ hden).2
  calc
    _ ≤ 4 * (N : ℝ) ^ 2 := hsum
    _ = 2 * (N : ℝ) * (2 * N : ℝ) := by ring

/-- The de la Vallée-Poussin combination `2 F_(2N) - F_N` has uniformly
bounded discrete absolute mass on every translated midpoint grid. -/
theorem shifted_v_fejer_average_abs_le_five (N : ℕ) (t : ℝ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N,
      |2 * (Complex.normSq
          (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t) /
            (2 * N : ℝ)) -
        (Complex.normSq
          (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) /
            (N : ℝ))|) / N ≤ 5 := by
  let f₂ : ℕ → ℝ := fun j => Complex.normSq
    (∑ r ∈ Finset.range (2 * N), shiftedMidpointCharacter N r j t) / (2 * N : ℝ)
  let f₁ : ℕ → ℝ := fun j => Complex.normSq
    (∑ r ∈ Finset.range N, shiftedMidpointCharacter N r j t) / (N : ℝ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass1 : (∑ j ∈ Finset.range N, f₁ j) / N = 1 := by
    simpa [f₁] using shifted_fejer_average_eq_one N t hN
  have hmass2 : (∑ j ∈ Finset.range N, f₂ j) / N ≤ 2 := by
    simpa [f₂] using shifted_double_fejer_average_le_two N t hN
  have hf₁ (j : ℕ) : 0 ≤ f₁ j := by
    dsimp [f₁]
    exact div_nonneg (Complex.normSq_nonneg _) (by positivity)
  have hf₂ (j : ℕ) : 0 ≤ f₂ j := by
    dsimp [f₂]
    exact div_nonneg (Complex.normSq_nonneg _) (by positivity)
  have hsum :
      (∑ j ∈ Finset.range N, |2 * f₂ j - f₁ j|) ≤
        2 * (∑ j ∈ Finset.range N, f₂ j) +
          (∑ j ∈ Finset.range N, f₁ j) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, (2 * f₂ j + f₁ j) := by
            apply Finset.sum_le_sum
            intro j hj
            calc
              |2 * f₂ j - f₁ j| ≤ |2 * f₂ j| + |f₁ j| :=
                by simpa only [sub_zero, zero_sub, abs_neg] using
                  abs_sub_le (2 * f₂ j) 0 (f₁ j)
              _ = 2 * f₂ j + f₁ j := by rw [abs_of_nonneg (mul_nonneg (by norm_num) (hf₂ j)),
                abs_of_nonneg (hf₁ j)]
      _ = 2 * (∑ j ∈ Finset.range N, f₂ j) +
            (∑ j ∈ Finset.range N, f₁ j) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmass1' : (∑ j ∈ Finset.range N, f₁ j) = N := by
    have h := (div_eq_iff hNpos.ne').mp hmass1
    nlinarith
  have hmass2' : (∑ j ∈ Finset.range N, f₂ j) ≤ 2 * N :=
    (div_le_iff₀ hNpos).mp hmass2
  apply (div_le_iff₀ hNpos).2
  calc
    _ ≤ 2 * (∑ j ∈ Finset.range N, f₂ j) +
          (∑ j ∈ Finset.range N, f₁ j) := hsum
    _ ≤ 5 * N := by nlinarith
end HaarQuarter.TheoremD.Fejer


namespace HaarQuarter.TheoremD.Fejer

open scoped BigOperators

/-- Number of pairs of modes in `[0,N)` with a fixed nonnegative difference. -/
theorem mode_difference_count (N q : ℕ) (hq : q ≤ N) :
    (∑ s ∈ Finset.range N, ∑ r ∈ Finset.range N,
      (if (r : ℤ) - (s : ℤ) = (q : ℤ) then (1 : ℝ) else 0)) =
      ((N - q : ℕ) : ℝ) := by
  classical
  have hinner (s : ℕ) :
      (∑ r ∈ Finset.range N,
        (if (r : ℤ) - (s : ℤ) = (q : ℤ) then (1 : ℝ) else 0)) =
      if s + q < N then 1 else 0 := by
    have heq (r : ℕ) : ((r : ℤ) - (s : ℤ) = (q : ℤ)) ↔ r = s + q := by omega
    simp_rw [heq]
    simp
  simp_rw [hinner]
  have hfilter : (Finset.range N).filter (fun s => s + q < N) = Finset.range (N - q) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    (∑ s ∈ Finset.range N, if s + q < N then (1 : ℝ) else 0) =
        ∑ s ∈ (Finset.range N).filter (fun s => s + q < N), (1 : ℝ) := by
          rw [Finset.sum_filter]
    _ = ((N - q : ℕ) : ℝ) := by rw [hfilter]; simp

/-- Reversing the two modes changes only the sign of the difference. -/
theorem mode_difference_count_neg (N q : ℕ) (hq : q ≤ N) :
    (∑ s ∈ Finset.range N, ∑ r ∈ Finset.range N,
      (if (r : ℤ) - (s : ℤ) = -(q : ℤ) then (1 : ℝ) else 0)) =
      ((N - q : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  have heq (s r : ℕ) : ((r : ℤ) - (s : ℤ) = -(q : ℤ)) ↔
      (s : ℤ) - (r : ℤ) = (q : ℤ) := by omega
  simp_rw [heq]
  exact mode_difference_count N q hq

end HaarQuarter.TheoremD.Fejer
