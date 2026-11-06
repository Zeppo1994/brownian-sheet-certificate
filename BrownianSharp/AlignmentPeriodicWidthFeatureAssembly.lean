import BrownianSharp.AlignmentPeriodicWidthRealification
import BrownianSharp.AlignmentPeriodicWidthLayerAlgebra
import BrownianSharp.AlignmentPartitionDictionary
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentFourierLipschitz
import BrownianSharp.AlignmentQuantitativeTorusSampling
import Mathlib.Topology.ContinuousMap.Compact

/-! A continuous-function version of graded finite Hilbert-dictionary assembly.
The partition-of-unity interpolation contributes only the feature oscillation;
the rank and graded dictionary error are inherited from the finite sampled
problem. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPeriodicWidthFeatureAssembly

open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.AlignmentHilbertDictionary
open BrownianSharp.AlignmentPeriodicWidthLayerAlgebra
open BrownianSharp.AlignmentPeriodicWidthRealification
open BrownianSharp.AlignmentTorusSampling
open BrownianSharp.AlignmentPeriodicRealEnergy
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus

theorem real_periodic_block_tail_error {d : ℕ} (r : ℝ) (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f)
    (S : Finset (Fin d → ℕ)) {ε : ℝ}
    (htail : ∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖ ≤ ε) :
    ∀ t, |(complexifyContinuous f t).re -
      ∑ s ∈ S, (block s f t).re| ≤ ε := by
  classical
  have hhas := AlignmentPeriodicFourierReconstruction.sobolev_two_blocks_hasSum
    r hr f hf
  have hs := hhas.summable
  have hq0 : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2:ℝ)^(1/2-r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hmajor : Summable (fun s : Fin d → ℕ =>
      Real.sqrt ((5:ℝ)^d) * ((2:ℝ)^(1/2-r))^(∑ i, s i)) :=
    (AlignmentPeriodicReconstruction.summable_shape_geometric d hq0 hq1).mul_left
      (Real.sqrt ((5:ℝ)^d))
  have hnorm : Summable (fun s : Fin d → ℕ => ‖block s f‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s =>
      AlignmentPeriodicReconstruction.nikolsky_two_block_sup_bound s f r
        (AlignmentPeriodicEnergy.sobolev_two_subset_nikolsky_two r f hf))
  have hdecomp := hs.sum_add_tsum_compl (s := S)
  rw [hhas.tsum_eq] at hdecomp
  have htailnorm : ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f‖ ≤ ε := by
    calc
      _ ≤ ∑' s : (Sᶜ : Set (Fin d → ℕ)), ‖block s.1 f‖ :=
        norm_tsum_le_tsum_norm (hnorm.subtype _)
      _ ≤ ε := htail
  intro t
  have hEval : (∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f) t =
      ∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t := by
    simpa using (ContinuousMap.evalCLM ℝ t).map_tsum (hs.subtype _)
  have hpw := congrArg (fun g : C(UnitAddTorus (Fin d), ℂ) => g t) hdecomp
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply, hEval] at hpw
  have hpwRe := congrArg Complex.re hpw
  rw [Complex.add_re, Complex.re_sum] at hpwRe
  have hreal : (complexifyContinuous f t).re -
      ∑ s ∈ S, (block s f t).re =
      (∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t).re := by
    linarith
  rw [hreal]
  calc
    |(∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t).re| ≤
      ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f t‖ := Complex.abs_re_le_norm _
    _ = ‖(∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f) t‖ := by rw [hEval]
    _ ≤ ‖∑' s : (Sᶜ : Set (Fin d → ℕ)), block s.1 f‖ :=
      ContinuousMap.norm_coe_le_norm _ t
    _ ≤ ε := htailnorm

theorem shape_grade_card_le_power_pred {d : ℕ} (hd : 0<d)
    (S : Finset (Fin d → ℕ)) (n : ℕ) :
    (S.filter (fun s => (∑ i, s i) = n)).card ≤ (n+1)^(d-1) := by
  classical
  cases d with
  | zero => simp at hd
  | succ k =>
    let U : Finset (Fin (k+1) → ℕ) :=
      S.filter (fun s => (∑ i, s i) = n)
    let T : Type := {s : Fin (k+1) → ℕ // s ∈ U}
    let e : T → (Fin k → Fin (n+1)) := fun s j =>
      ⟨s.1 j.castSucc, by
        have hcoord : s.1 j.castSucc ≤ ∑ i, s.1 i :=
          Finset.single_le_sum (fun i hi => Nat.zero_le (s.1 i)) (Finset.mem_univ _)
        have hgrade := (Finset.mem_filter.mp s.2).2
        rw [hgrade] at hcoord
        omega⟩
    have he : Function.Injective e := by
      intro s t h
      apply Subtype.ext
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hcoord : ∀ i : Fin k, s.1 i.castSucc = t.1 i.castSucc := by
          intro i
          exact congrArg Fin.val (congrFun h i)
        have hs := (Finset.mem_filter.mp s.2).2
        have ht := (Finset.mem_filter.mp t.2).2
        rw [Fin.sum_univ_castSucc] at hs ht
        have hsum : (∑ i : Fin k, s.1 i.castSucc) =
            ∑ i : Fin k, t.1 i.castSucc := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoord i
        omega
      · exact congrArg Fin.val (congrFun h i)
    have hcard := Fintype.card_le_of_injective e he
    have hT : Fintype.card T=U.card := Fintype.card_coe U
    rw [hT] at hcard
    have hattach : (S.filter (fun s => (∑ i, s i)=n)).card=U.card := rfl
    rw [hattach]
    simpa [Fintype.card_fun] using hcard

/-- Coordinate box of dyadic shapes with each coordinate at most T. -/
def periodicShapeBox {d : ℕ} (T : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.range (T+1))

/-- The finite simplex of shapes whose total grade is at most T. -/
def periodicShapeSimplex {d : ℕ} (T : ℕ) : Finset (Fin d → ℕ) :=
  (periodicShapeBox T).filter (fun s => (∑ j, s j) ≤ T)

theorem mem_periodicShapeSimplex {d T : ℕ} (s : Fin d → ℕ) :
    s ∈ periodicShapeSimplex T ↔ (∑ j, s j) ≤ T := by
  classical
  unfold periodicShapeSimplex periodicShapeBox
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      apply Finset.mem_range.mpr
      have hcoord := Finset.single_le_sum
        (fun i hi => Nat.zero_le (s i)) (Finset.mem_univ j)
      omega
    · exact h

theorem periodic_box_grade_le {d T : ℕ} {s : Fin d → ℕ}
    (hs : s ∈ periodicShapeBox T) : (∑ j, s j) ≤ d*T := by
  classical
  unfold periodicShapeBox at hs
  have hcoord : ∀ j, s j ≤ T := by
    intro j
    have hj := Fintype.mem_piFinset.mp hs j
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc
    (∑ j, s j) ≤ ∑ _j : Fin d, T := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = d*T := by simp

private theorem sum_two_pow_range_le (M : ℕ) :
    (∑ n ∈ Finset.range M, 2^n) ≤ 2^M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hpow : 2^M + 2^M = 2^(M+1) := by rw [pow_succ]; ring
      omega

private theorem periodic_grade_count_simple {d : ℕ} (hd : 0<d)
    (S : Finset (Fin d → ℕ)) (n : ℕ) :
    (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 =>
      coefficientGrade i.1=n)).card ≤ 2*5^d*2^n*(n+1)^(d-1) := by
  classical
  let U : Finset (Fin d → ℕ) := S.filter (fun s => (∑ j,s j)=n)
  let T : Type := {s : Fin d → ℕ // s∈U}
  let e : {i : FourierCoeffIndex S × Fin 2 // coefficientGrade i.1=n} →
      Σ s : T, frequencyBox s.1 × Fin 2 := fun i =>
    ⟨⟨i.1.1.1.1, by
      have hs := i.1.1.1.2
      have hn := i.2
      exact Finset.mem_filter.mpr ⟨hs, hn⟩⟩, (i.1.1.2, i.1.2)⟩
  let back : (Σ s : T, frequencyBox s.1 × Fin 2) → FourierCoeffIndex S × Fin 2 :=
    fun z => (⟨⟨z.1.1, (Finset.mem_filter.mp z.1.2).1⟩, z.2.1⟩, z.2.2)
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    have hb := congrArg back h
    have hx : back (e x)=x.1 := by simp [back,e]
    have hy : back (e y)=y.1 := by simp [back,e]
    rw [hx,hy] at hb
    exact hb
  have hcardinj := Fintype.card_le_of_injective e he
  have htarget : Fintype.card (Σ s : T, frequencyBox s.1 × Fin 2) =
      ∑ s : T, (frequencyBox s.1).card*2 := by
    simp [Fintype.card_sigma,Fintype.card_prod]
  have hbox : ∀ s : T, (frequencyBox s.1).card ≤ 5^d*2^n := by
    intro s
    have hc := AlignmentPeriodicReconstruction.frequencyBox_card_le s.1
    have hn : ∑ j,s.1 j=n := (Finset.mem_filter.mp s.2).2
    rw [hn] at hc
    exact hc
  have hsum : (∑ s : T, (frequencyBox s.1).card*2) ≤
      Fintype.card T*(5^d*2^n*2) := by
    calc
      _ ≤ ∑ _s : T, (5^d*2^n*2) := by
        apply Finset.sum_le_sum
        intro s hs
        nlinarith [hbox s]
      _ = _ := by simp
  have hT : Fintype.card T ≤ (n+1)^(d-1) := by
    have hco : Fintype.card T=U.card := Fintype.card_coe U
    rw [hco]
    exact shape_grade_card_le_power_pred hd S n
  have hfinal : Fintype.card T*(5^d*2^n*2) ≤
      2*5^d*2^n*(n+1)^(d-1) := by
    calc
      _ ≤ (n+1)^(d-1)*(5^d*2^n*2) := Nat.mul_le_mul_right _ hT
      _ = _ := by ring
  have hfilter : Fintype.card {i : FourierCoeffIndex S × Fin 2 //
      coefficientGrade i.1=n} =
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 =>
        coefficientGrade i.1=n)).card := by
    exact Fintype.card_ofFinset
      (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 =>
        coefficientGrade i.1=n))
      (by intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change (coefficientGrade i.1=n) ↔ i ∈ {x | coefficientGrade x.1=n}
          rw [Set.mem_ofPred_eq])
  calc
    _ = Fintype.card {i : FourierCoeffIndex S × Fin 2 // coefficientGrade i.1=n} := by
      symm; exact hfilter
    _ ≤ Fintype.card (Σ s : T, frequencyBox s.1 × Fin 2) := hcardinj
    _ = ∑ s : T, (frequencyBox s.1).card*2 := htarget
    _ ≤ Fintype.card T*(5^d*2^n*2) := hsum
    _ ≤ 2*5^d*2^n*(n+1)^(d-1) := hfinal

/-- Sharp polynomial count for the retained low-grade Fourier coordinates.
The degree is d−1 because a fixed total grade is a simplex boundary. -/
theorem periodic_low_frequency_card_le_sharp {d M : ℕ} (hd : 0<d)
    (S : Finset (Fin d → ℕ))
    (σ : FourierCoeffIndex S × Fin 2 → Option ℕ)
    (hbelow : ∀ i, σ i = none → coefficientGrade i.1 < M) :
    Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i = none} ≤
      2*5^d*(M+1)^(d-1)*2^M := by
  classical
  let α := {i : FourierCoeffIndex S × Fin 2 // σ i = none}
  let g : α → Fin M := fun x => ⟨coefficientGrade x.1.1, hbelow x.1 x.2⟩
  have hdecomp : Fintype.card α =
      ∑ n : Fin M, Fintype.card {x : α // g x=n} := by
    calc
      Fintype.card α = Fintype.card ((n : Fin M) × {x : α // g x=n}) := by
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv g).symm
      _ = ∑ n : Fin M, Fintype.card {x : α // g x=n} := Fintype.card_sigma
  have hfiber : ∀ n : Fin M,
      Fintype.card {x : α // g x=n} ≤
        2*5^d*2^(n.val)*(n.val+1)^(d-1) := by
    intro n
    let τ : FourierCoeffIndex S × Fin 2 → Option ℕ :=
      fun i => some (coefficientGrade i.1)
    have hτ : ∀ i m, τ i=some m → coefficientGrade i.1=m := by
      intro i m h
      simpa [τ] using h
    have hc := periodic_grade_count_simple hd S n.val
    let e : {x : α // g x=n} → {i : FourierCoeffIndex S × Fin 2 // τ i=some n.val} :=
      fun x => ⟨x.1.1, by
        have hv : coefficientGrade x.1.1.1=n.val := congrArg Fin.val x.2
        simp [τ, hv]⟩
    have he : Function.Injective e := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {i : FourierCoeffIndex S × Fin 2 // τ i=some n.val} => z.1) h
    have hcardinj := Fintype.card_le_of_injective e he
    have hcardfilter : Fintype.card {i : FourierCoeffIndex S × Fin 2 // τ i=some n.val} =
        (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => τ i=some n.val)).card := by
      exact Fintype.card_ofFinset
        (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => τ i=some n.val))
        (by intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            change (τ i=some n.val) ↔ i ∈ {x | τ x=some n.val}
            rw [Set.mem_ofPred_eq])
    rw [hcardfilter] at hcardinj
    exact hcardinj.trans (by simpa [τ] using hc)
  have hsum : (∑ n : Fin M, (2*5^d*2^(n.val)*(n.val+1)^(d-1):ℕ)) ≤
      2*5^d*(M+1)^(d-1)*2^M := by
    calc
      (∑ n : Fin M, 2*5^d*2^(n.val)*(n.val+1)^(d-1)) =
          ∑ n ∈ Finset.range M, 2*5^d*2^n*(n+1)^(d-1) := by
        exact Fin.sum_univ_eq_sum_range
          (fun n => 2*5^d*2^n*(n+1)^(d-1)) M
      _ ≤
          ∑ n ∈ Finset.range M, 2*5^d*2^n*(M+1)^(d-1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnM : n < M := Finset.mem_range.mp hn
        have hpoly : n+1 ≤ M+1 := by omega
        exact Nat.mul_le_mul_left (2*5^d*2^n)
          (Nat.pow_le_pow_left hpoly (d-1))
      _ = 2*5^d*(M+1)^(d-1)*(∑ n ∈ Finset.range M, 2^n) := by
        calc
          _ = ∑ n ∈ Finset.range M, 2^n*(2*5^d*(M+1)^(d-1)) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = (∑ n ∈ Finset.range M, 2^n)*(2*5^d*(M+1)^(d-1)) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
      _ ≤ 2*5^d*(M+1)^(d-1)*2^M := by
        exact Nat.mul_le_mul_left _ (sum_two_pow_range_le M)
  calc
    Fintype.card α = ∑ n : Fin M, Fintype.card {x : α // g x=n} := hdecomp
    _ ≤ ∑ n : Fin M, 2*5^d*2^(n.val)*(n.val+1)^(d-1) :=
      Finset.sum_le_sum (fun n _ => hfiber n)
    _ ≤ 2*5^d*(M+1)^(d-1)*2^M := hsum

theorem periodic_feature_radius_energy_identity (d k n : ℕ) (r : ℝ) :
    (Real.sqrt ((2*5^d*2^n*(n+1)^k:ℕ):ℝ) *
      (2:ℝ)^(-r*(n:ℝ)))^2 =
      (2*(5:ℝ)^d)*((n+1:ℕ):ℝ)^k*((2:ℝ)^(1-2*r))^n := by
  have hpow : (2:ℝ)^n*((2:ℝ)^(-r*(n:ℝ)))^2 =
      ((2:ℝ)^(1-2*r))^n := by
    have hpowleft : (2:ℝ)^n = Real.rpow 2 (n:ℝ) := by
      exact (Real.rpow_natCast (2:ℝ) n).symm
    have hpowsquare : ((2:ℝ)^(-r*(n:ℝ)))^2 =
        Real.rpow 2 ((-r*(n:ℝ))*2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      simp
    rw [hpowleft, hpowsquare]
    have hexp : (n:ℝ)+(-r*(n:ℝ))*2=(1-2*r)*(n:ℝ) := by ring
    calc
      _ = Real.rpow 2 ((n:ℝ)+(-r*(n:ℝ))*2) :=
        (Real.rpow_add (by norm_num : (0:ℝ)<2) (n:ℝ)
          ((-r*(n:ℝ))*2)).symm
      _ = Real.rpow 2 ((1-2*r)*(n:ℝ)) := by rw [hexp]
    have hpowright : ((2:ℝ)^(1-2*r))^n = (2:ℝ)^((1-2*r)*(n:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    exact hpowright.symm
  rw [mul_pow, Real.sq_sqrt (by positivity :
      0 ≤ ((2*5^d*2^n*(n+1)^k:ℕ):ℝ))]
  push_cast
  calc
    _ = (2*(5:ℝ)^d*((n+1:ℕ):ℝ)^k) *
        ((2:ℝ)^n*((2:ℝ)^(-r*(n:ℝ)))^2) := by norm_num [Nat.cast_add]; ring
    _ = _ := by rw [hpow]; norm_num [Nat.cast_add]

/-- Frequency-coordinate count for a single grade, reduced to the number of
shapes at that grade. -/
theorem periodic_grade_coordinate_count_le
    {d : ℕ} (S : Finset (Fin d → ℕ))
    (hd : 0<d)
    (σ : (FourierCoeffIndex S × Fin 2) → Option ℕ)
    (shift : ℕ)
    (hgrade : ∀ i n, σ i = some n → coefficientGrade i.1 = shift+n)
    (n : ℕ)
    (hshape : (S.filter (fun s => (∑ j, s j) = shift+n)).card ≤ (shift+n+1)^(d-1)) :
    (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i = some n)).card ≤
      2*5^d*2^(shift+n)*(shift+n+1)^(d-1) := by
  classical
  let U : Finset (Fin d → ℕ) := S.filter (fun s => (∑ j, s j) = shift+n)
  let T : Type := {s : Fin d → ℕ // s ∈ U}
  let e : {i : FourierCoeffIndex S × Fin 2 // σ i = some n} →
      Σ s : T, frequencyBox s.1 × Fin 2 := fun i =>
    ⟨⟨i.1.1.1.1, by
      have hg := hgrade i.1 n i.2
      have hg' : (∑ j, i.1.1.1.1 j) = shift+n := by
        simpa [coefficientGrade] using hg
      exact Finset.mem_filter.mpr ⟨i.1.1.1.2, hg'⟩⟩,
      (i.1.1.2, i.1.2)⟩
  let back : (Σ s : T, frequencyBox s.1 × Fin 2) → FourierCoeffIndex S × Fin 2 :=
    fun z => (⟨⟨z.1.1, (Finset.mem_filter.mp z.1.2).1⟩, z.2.1⟩, z.2.2)
  have heinj : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    have h' := congrArg back h
    have hx : back (e x) = x.1 := by simp [back, e]
    have hy : back (e y) = y.1 := by simp [back, e]
    rw [hx, hy] at h'
    exact h'
  have hcardinj := Fintype.card_le_of_injective e heinj
  have hcardTarget : Fintype.card (Σ s : T, frequencyBox s.1 × Fin 2) =
      ∑ s : T, (frequencyBox s.1).card*2 := by
    simp [Fintype.card_sigma, Fintype.card_prod]
  have hbox : ∀ s : T, (frequencyBox s.1).card ≤ 5^d*2^(shift+n) := by
    intro s
    have h := AlignmentPeriodicReconstruction.frequencyBox_card_le s.1
    have hgrade' : ∑ j, s.1 j = shift+n := (Finset.mem_filter.mp s.2).2
    rw [hgrade'] at h
    exact h
  have hsum : (∑ s : T, (frequencyBox s.1).card*2) ≤
      Fintype.card T*(5^d*2^(shift+n)*2) := by
    calc
      _ ≤ ∑ _s : T, (5^d*2^(shift+n)*2) := by
        apply Finset.sum_le_sum
        intro s hs
        nlinarith [hbox s]
      _ = _ := by simp
  have hcardT : Fintype.card T ≤ (shift+n+1)^(d-1) := by
    have hT : Fintype.card T = U.card := Fintype.card_coe U
    rw [hT]
    exact hshape
  have hfinal : Fintype.card T*(5^d*2^(shift+n)*2) ≤
      2*5^d*2^(shift+n)*(shift+n+1)^(d-1) := by
    calc
      Fintype.card T*(5^d*2^(shift+n)*2) ≤
          (shift+n+1)^(d-1)*(5^d*2^(shift+n)*2) :=
        Nat.mul_le_mul_right _ hcardT
      _ = 2*5^d*2^(shift+n)*(shift+n+1)^(d-1) := by ring
  calc
    _ = Fintype.card {i : FourierCoeffIndex S × Fin 2 // σ i = some n} := by
      symm
      exact Fintype.card_ofFinset
        (Finset.univ.filter (fun i : FourierCoeffIndex S × Fin 2 => σ i = some n))
        (by intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            change (σ i = some n) ↔ i ∈ {x | σ x = some n}
            rw [Set.mem_ofPred_eq])
    _ ≤ Fintype.card (Σ s : T, frequencyBox s.1 × Fin 2) := hcardinj
    _ = ∑ s : T, (frequencyBox s.1).card*2 := hcardTarget
    _ ≤ Fintype.card T*(5^d*2^(shift+n)*2) := hsum
    _ ≤ 2*5^d*2^(shift+n)*(shift+n+1)^(d-1) := hfinal

theorem partition_geometric_hilbert_layer_approximation
    {α I G : Type} [TopologicalSpace α] [CompactSpace α]
    [Fintype I] [Fintype G]
    (v : α → EuclideanSpace ℝ I)
    (φ : G → C(α, ℝ)) (a : G → α)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {L : ℕ} (σ : I → Option (Fin L)) (R : Fin L → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g, ‖coordinateLayerMask σ (some j) (v (a g))‖ ≤ R j)
    {A₀ ρ q : ℝ} {k : ℕ} (hA₀ : 0 ≤ A₀)
    (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1)
    (hρq : ρ < q)
    (henergy : ∀ j, (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val))
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : I // σ i = none} ≤ D)
    {δ : ℝ}
    (hosc : ∀ i t, φ i t ≠ 0 → ‖v t-v (a i)‖ ≤ δ) :
    ∃ W : Submodule ℝ C(α, ℝ),
      Module.rank ℝ W ≤ (D*Nat.ceil (1+(1-q)⁻¹):Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ 1 → ∃ y ∈ W,
        ∀ t, |⟪x,v t⟫ - y t| ≤ δ + Real.sqrt (
          (4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) k) := by
  classical
  obtain ⟨V,hVrank,hVapprox⟩ :=
    finite_geometric_hilbert_layer_dictionary_assembly
      (C:=10000) (by norm_num) hq hq1 hρ hρq hA₀ hD
      σ (fun g => v (a g)) R hR hrow henergy hlow
  let E : (G → ℝ) →L[ℝ] C(α,ℝ) := partitionReconstruction φ
  refine ⟨V.map E.toLinearMap, ?_, ?_⟩
  · simpa [Nat.cast_mul] using (rank_map_le E.toLinearMap V).trans hVrank
  intro x hx
  obtain ⟨z,hz,herr⟩ := hVapprox x hx
  refine ⟨E z, Submodule.mem_map.mpr ⟨z,hz,rfl⟩, ?_⟩
  intro t
  let f : G → ℝ := fun i => ⟪x,v (a i)⟫
  have hlocal : |⟪x,v t⟫ - E f t| ≤ δ := by
    have hid : ⟪x,v t⟫ - E f t =
        ∑ i, φ i t * ⟪x,v t-v (a i)⟫ := by
      simp only [E, partitionReconstruction_apply, inner_sub_right]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hid]
    calc
      |∑ i, φ i t * ⟪x,v t-v (a i)⟫| =
          ‖∑ i, φ i t * ⟪x,v t-v (a i)⟫‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ i, ‖φ i t * ⟪x,v t-v (a i)⟫‖ := norm_sum_le _ _
      _ = ∑ i, |φ i t * ⟪x,v t-v (a i)⟫| := by simp [Real.norm_eq_abs]
      _ ≤ ∑ i, φ i t * δ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzφ : φ i t = 0
        · simp [hzφ]
        · rw [abs_mul, abs_of_nonneg (hφ i t)]
          apply mul_le_mul_of_nonneg_left _ (hφ i t)
          have hinner := abs_real_inner_le_norm x (v t-v (a i))
          have hprod := mul_le_mul hx (hosc i t hzφ)
            (norm_nonneg (v t-v (a i))) (by norm_num : 0 ≤ (1:ℝ))
          exact hinner.trans (by nlinarith)
      _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]
  have hfeq : finiteRowLinear (fun g => v (a g)) x = f := by
    funext i
    rfl
  rw [hfeq] at herr
  calc
    |⟪x,v t⟫ - E z t| ≤ |⟪x,v t⟫-E f t| + |E f t-E z t| := abs_sub_le _ _ _
    _ ≤ δ + ‖E (f-z)‖ := by
      apply add_le_add hlocal
      simpa only [map_sub, ContinuousMap.sub_apply, Real.norm_eq_abs] using
        (ContinuousMap.norm_coe_le_norm (E (f-z)) t)
    _ ≤ δ + ‖f-z‖ := by
      simpa [add_comm] using
        add_le_add_left (partitionReconstruction_contractile φ hφ hsum (f-z)) δ
    _ ≤ δ + Real.sqrt (
          (4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) k) := by
      simpa [add_comm] using add_le_add_right herr δ

end BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
