import BrownianSharp.AlignmentPaperContinuumGenericBump
import BrownianSharp.AlignmentEndpointYoung
import BrownianSharp.PeriodicAtomDerivatives
import BrownianSharp.AlignmentPaperTorusTranslation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! A generic smooth bump interface and its actual dyadic derivative envelopes.
This is the analytic input for the general-bump periodic synthesis endpoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperGenericSmoothBumpBesov

open BrownianSharp
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.ScalarHighFrequency
open BrownianSharp.ScalarAtomVariance
open BrownianSharp.ScalarKernelL1
open BrownianSharp.AtomicBlockVariance
open BrownianSharp.AlignmentPaperContinuumGenericBump

private theorem prod_le_prod_nonneg_real {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (hle i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hle j (Finset.mem_insert_of_mem hj)))
        (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (hg i (Finset.mem_insert_self _ _))

/-- A real smooth compactly supported atom whose topological support lies
strictly inside the unit interval. -/
structure SmoothCompactBump where
  atom : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) atom
  tsupport_subset : tsupport atom ⊆ Set.Ioo (0 : ℝ) 1

def dyadicLift (ψ : SmoothCompactBump) (s j : ℕ) (x : ℝ) : ℝ :=
  ψ.atom ((2 : ℝ)^s * x - (j : ℝ))

theorem iteratedDeriv_dyadicLift (ψ : SmoothCompactBump) (s j k : ℕ) :
    iteratedDeriv k (dyadicLift ψ s j) = fun x =>
      (2 : ℝ)^(s*k) * iteratedDeriv k ψ.atom ((2 : ℝ)^s*x-(j:ℝ)) := by
  let c : ℝ := (2:ℝ)^s
  let g : ℝ → ℝ := fun y => ψ.atom (y-(j:ℝ))
  have haffine : ContDiff ℝ (⊤:ℕ∞) (fun y:ℝ => y-(j:ℝ)) := by fun_prop
  have hgTop : ContDiff ℝ (⊤:ℕ∞) g := by
    change ContDiff ℝ (⊤:ℕ∞) (ψ.atom ∘ fun y:ℝ => y-(j:ℝ))
    exact ContDiff.comp ψ.smooth haffine
  have hscale := iteratedDeriv_comp_const_mul (n:=k) (f:=g)
    (hgTop.of_le (by simp)) c
  have hoffset := iteratedDeriv_comp_sub_const (n:=k) (f:=ψ.atom) (s:=(j:ℝ))
  funext x
  have h := congrFun hscale x
  have ho := congrFun hoffset (c*x)
  change iteratedDeriv k (fun x:ℝ => ψ.atom ((2:ℝ)^s*x-(j:ℝ))) x = _
  rw [show (fun x:ℝ => ψ.atom ((2:ℝ)^s*x-(j:ℝ))) = (fun x => g (c*x)) by
    funext y; simp [g,c]]
  rw [h, ho]
  rw [show c^k=(2:ℝ)^(s*k) by dsimp [c]; rw [← pow_mul]]

theorem iteratedDeriv_eq_zero_of_not_tsupport (ψ : SmoothCompactBump) (k : ℕ)
    {x : ℝ} (hx : x ∉ tsupport ψ.atom) : iteratedDeriv k ψ.atom x = 0 := by
  have hclosed : IsClosed (tsupport ψ.atom) := isClosed_tsupport ψ.atom
  let U := (tsupport ψ.atom)ᶜ
  have hU : IsOpen U := hclosed.isOpen_compl
  have hxU : x ∈ U := hx
  have hEq : Set.EqOn ψ.atom (fun _ : ℝ => 0) U := by
    intro y hy
    have hnot : y ∉ Function.support ψ.atom := by
      intro hs
      have hclose : y ∈ closure (Function.support ψ.atom) := subset_closure hs
      exact hy (by simpa [tsupport] using hclose)
    simpa [Function.mem_support] using hnot
  calc
    iteratedDeriv k ψ.atom x = iteratedDerivWithin k ψ.atom U x :=
      (iteratedDerivWithin_of_isOpen hU hxU).symm
    _ = iteratedDerivWithin k (fun _ : ℝ => 0) U x :=
      iteratedDerivWithin_congr hEq hxU
    _ = 0 := by simp

theorem exists_derivative_envelope (ψ : SmoothCompactBump) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |iteratedDeriv k ψ.atom x| ≤ C := by
  let f : ℝ → ℝ := fun x => |iteratedDeriv k ψ.atom x|
  have hf : Continuous f := (ψ.smooth.continuous_iteratedDeriv k (by simp)).abs
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0, by simp⟩) hf.continuousOn
  let C := f x₀ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x
  by_cases hx : x ∈ Set.Icc (0:ℝ) 1
  · calc
      f x ≤ f x₀ := hmax hx
      _ ≤ C := by dsimp [C]; linarith
  · have hout : x ≤ 0 ∨ 1 ≤ x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact Or.inl hx.le
      · exact Or.inr hx.le
    have hnot : x ∉ tsupport ψ.atom := by
      intro h
      have hs := ψ.tsupport_subset h
      rcases hout with hleft | hright
      · linarith [hs.1]
      · linarith [hs.2]
    rw [iteratedDeriv_eq_zero_of_not_tsupport ψ k hnot]
    simp [f, C]
    positivity

/-- The actual periodization of the `k`th derivative of a generic bump at
dyadic address `(s,j)`. -/
noncomputable def periodizedDerivative (ψ : SmoothCompactBump) (s j : ℕ)
    (hj : j < 2^s) (k : ℕ) : C(UnitAddCircle, ℝ) := by
  let f : ℝ → ℝ := iteratedDeriv k (dyadicLift ψ s j)
  have hfend : f 0 = f 1 := by
    rw [show f = iteratedDeriv k (dyadicLift ψ s j) by rfl,
      iteratedDeriv_dyadicLift]
    have hleft : (2:ℝ)^s*0-(j:ℝ) ≤ 0 := by simp
    have hj' : j+1 ≤ 2^s := Nat.succ_le_of_lt hj
    have hjr : (j:ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast hj'
    have hright : 1 ≤ (2:ℝ)^s*1-(j:ℝ) := by nlinarith
    have hx0 : (2:ℝ)^s*0-(j:ℝ) ∉ tsupport ψ.atom := by
      intro h
      have h' := ψ.tsupport_subset h
      linarith [h'.1]
    have hx1 : (2:ℝ)^s*1-(j:ℝ) ∉ tsupport ψ.atom := by
      intro h
      have h' := ψ.tsupport_subset h
      linarith [h'.2]
    change (2:ℝ)^(s*k) * iteratedDeriv k ψ.atom ((2:ℝ)^s*0-(j:ℝ)) =
      (2:ℝ)^(s*k) * iteratedDeriv k ψ.atom ((2:ℝ)^s*1-(j:ℝ))
    rw [iteratedDeriv_eq_zero_of_not_tsupport ψ k hx0,
      iteratedDeriv_eq_zero_of_not_tsupport ψ k hx1]
  have hcont : Continuous f := by
    have haffine : ContDiff ℝ (⊤:ℕ∞)
        (fun x:ℝ => (2:ℝ)^s*x-(j:ℝ)) := by fun_prop
    have htop : ContDiff ℝ (⊤:ℕ∞) (dyadicLift ψ s j) := by
      change ContDiff ℝ (⊤:ℕ∞) (ψ.atom ∘ fun x:ℝ => (2:ℝ)^s*x-(j:ℝ))
      exact ContDiff.comp ψ.smooth haffine
    exact htop.continuous_iteratedDeriv k (by simp)
  exact ⟨AddCircle.liftIco (1:ℝ) 0 f,
    AddCircle.liftIco_zero_continuous (p:=1) hfend hcont.continuousOn⟩

theorem periodizedDerivative_unit_interval (ψ : SmoothCompactBump) (s j : ℕ)
    (hj : j < 2^s) (k : ℕ) (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) 1) :
    periodizedDerivative ψ s j hj k (x : UnitAddCircle) =
      iteratedDeriv k (dyadicLift ψ s j) x := by
  change AddCircle.liftIco (1:ℝ) 0
    (iteratedDeriv k (dyadicLift ψ s j)) (x : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply hx

theorem periodizedDerivative_abs_le (ψ : SmoothCompactBump) (s j : ℕ)
    (hj : j < 2^s) (k : ℕ) (C : ℝ)
    (hC : ∀ x, |iteratedDeriv k ψ.atom x| ≤ C) (x : UnitAddCircle) :
    |periodizedDerivative ψ s j hj k x| ≤ C*(2:ℝ)^(s*k) := by
  let y : Set.Ico (0:ℝ) (0+1) := AddCircle.equivIco 1 0 x
  have hyx : (y.val : UnitAddCircle)=x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p:=1) (a:=0) (y:=x))
  have hy : y.val ∈ Set.Ico (0:ℝ) 1 := by simpa using y.property
  rw [← hyx, periodizedDerivative_unit_interval ψ s j hj k y.val hy,
    iteratedDeriv_dyadicLift]
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2:ℝ)^(s*k))]
  calc
    (2:ℝ)^(s*k) * |iteratedDeriv k ψ.atom ((2:ℝ)^s*y.val-(j:ℝ))| =
        |iteratedDeriv k ψ.atom ((2:ℝ)^s*y.val-(j:ℝ))| * (2:ℝ)^(s*k) := by ring
    _ ≤ C * (2:ℝ)^(s*k) := mul_le_mul_of_nonneg_right (hC _)
      (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)

theorem periodizedDerivative_complex_eq_lift (ψ : SmoothCompactBump) (s j : ℕ)
    (hj : j < 2^s) (k : ℕ) :
    (fun x : UnitAddCircle =>
      (periodizedDerivative ψ s j hj k x : ℂ)) =
    AddCircle.liftIco 1 0 (fun x : ℝ =>
      ((iteratedDeriv k (dyadicLift ψ s j) x : ℝ) : ℂ)) := by
  funext x
  let y : Set.Ico (0:ℝ) (0+1) := AddCircle.equivIco 1 0 x
  have hx : (y.val : UnitAddCircle) = x := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p:=(1:ℝ)) (a:=(0:ℝ)) (y:=x))
  rw [← hx]
  have hy : y.val ∈ Set.Ico (0:ℝ) 1 := by simpa using y.property
  rw [periodizedDerivative_unit_interval ψ s j hj k y.val hy,
    AddCircle.liftIco_coe_apply y.property]

theorem periodizedDerivative_fourier_step (ψ : SmoothCompactBump)
    (s j : ℕ) (hj : j < 2^s) (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle =>
      (periodizedDerivative ψ s j hj (k+1) x : ℂ)) n =
      (2*Real.pi*Complex.I*(n:ℂ)) * fourierCoeff
        (fun x : UnitAddCircle =>
          (periodizedDerivative ψ s j hj k x : ℂ)) n := by
  let f : ℝ → ℂ := fun x => ((iteratedDeriv k (dyadicLift ψ s j) x : ℝ) : ℂ)
  let f' : ℝ → ℂ := fun x =>
    ((iteratedDeriv (k+1) (dyadicLift ψ s j) x : ℝ) : ℂ)
  have htop : ContDiff ℝ (⊤:ℕ∞) (dyadicLift ψ s j) := by
    change ContDiff ℝ (⊤:ℕ∞) (ψ.atom ∘ fun x:ℝ => (2:ℝ)^s*x-(j:ℝ))
    exact ContDiff.comp ψ.smooth (by fun_prop)
  have hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    dsimp [f,f']
    have htop' : ContDiff ℝ (↑(k+1):ℕ∞) (dyadicLift ψ s j) :=
      htop.of_le (by simp)
    have hd := htop'.differentiable_iteratedDeriv' k
    have hda : HasDerivAt (iteratedDeriv k (dyadicLift ψ s j))
        (iteratedDeriv (k+1) (dyadicLift ψ s j) x) x := by
      have hh := (hd x).hasDerivAt
      simpa only [iteratedDeriv_succ] using hh
    exact hda.ofReal_comp
  have hend : f 0 = f 1 := by
    dsimp [f]
    rw [iteratedDeriv_dyadicLift]
    have hleft : (2:ℝ)^s*0-(j:ℝ) ≤ 0 := by simp
    have hj' : j+1≤2^s := Nat.succ_le_of_lt hj
    have hright : 1 ≤ (2:ℝ)^s*1-(j:ℝ) := by
      have hjr : (j:ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast hj'
      nlinarith
    have hx0 : (2:ℝ)^s*0-(j:ℝ) ∉ tsupport ψ.atom := by
      intro h; have hh := ψ.tsupport_subset h; linarith [hh.1]
    have hx1 : (2:ℝ)^s*1-(j:ℝ) ∉ tsupport ψ.atom := by
      intro h; have hh := ψ.tsupport_subset h; linarith [hh.2]
    simp only [iteratedDeriv_dyadicLift,
      iteratedDeriv_eq_zero_of_not_tsupport ψ k hx0,
      iteratedDeriv_eq_zero_of_not_tsupport ψ k hx1]
  have hcont : Continuous f' := by
    dsimp [f']
    exact Complex.continuous_ofReal.comp
      (htop.continuous_iteratedDeriv (k+1) (by simp))
  have hcoeff := fourierCoeff_liftIco_eq (T:=1) (a:=0) f n
  have hcoeff' := fourierCoeff_liftIco_eq (T:=1) (a:=0) f' n
  have hparts := fourierCoeffOn_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (by norm_num) hn (f:=f) (f':=f') (fun x _ => hfderiv x)
    (hcont.intervalIntegrable 0 1)
  have hparts' : fourierCoeffOn (by norm_num : (0:ℝ)<1) f n =
      (1/(-2*Real.pi*Complex.I*(n:ℂ))) *
        (fourier (-n) (0:UnitAddCircle) * (f 1-f 0) -
          (1:ℝ)*fourierCoeffOn (by norm_num : (0:ℝ)<1) f' n) := by
    simpa using hparts
  have hper0 := periodizedDerivative_complex_eq_lift ψ s j hj k
  have hper1 := periodizedDerivative_complex_eq_lift ψ s j hj (k+1)
  rw [hper1, hper0]
  have hcoeff1 : fourierCoeff (AddCircle.liftIco 1 0 f) n =
      fourierCoeffOn (by norm_num : (0:ℝ)<1) f n := by simpa [f] using hcoeff
  have hcoeff2 : fourierCoeff (AddCircle.liftIco 1 0 f') n =
      fourierCoeffOn (by norm_num : (0:ℝ)<1) f' n := by simpa [f'] using hcoeff'
  rw [hcoeff2,hcoeff1]
  have hend' : f 1-f 0=0 := by rw [hend]; ring
  rw [hend'] at hparts'
  have hparts'' := hparts'
  field_simp [hn] at hparts''
  have hrel : fourierCoeffOn (by norm_num : (0:ℝ)<1) f' n =
      (2*Real.pi*Complex.I*(n:ℂ)) * fourierCoeffOn
        (by norm_num : (0:ℝ)<1) f n := by
    have hh : fourierCoeffOn (by norm_num : (0:ℝ)<1) f n *
        (2*Real.pi*Complex.I*(n:ℂ)) =
          fourierCoeffOn (by norm_num : (0:ℝ)<1) f' n := by
      simpa [mul_assoc] using hparts''
    calc
      _ = fourierCoeffOn (by norm_num : (0:ℝ)<1) f n *
          (2*Real.pi*Complex.I*(n:ℂ)) := hh.symm
      _ = _ := by ring
  simpa [f,f'] using hrel

theorem periodizedDerivative_fourier_eq_pow (ψ : SmoothCompactBump)
    (s j : ℕ) (hj : j < 2^s) (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle =>
      (periodizedDerivative ψ s j hj k x : ℂ)) n =
      (2*Real.pi*Complex.I*(n:ℂ))^k * fourierCoeff
        (fun x : UnitAddCircle =>
          (periodizedDerivative ψ s j hj 0 x : ℂ)) n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [periodizedDerivative_fourier_step ψ s j hj k n hn, ih]
      rw [pow_succ]
      ring

theorem periodizedDerivative_zero_of_outside_cell (ψ : SmoothCompactBump)
    (s j : ℕ) (hj : j < 2^s) (k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Ico (0:ℝ) 1)
    (hout : x ≤ (j:ℝ)/(2:ℝ)^s ∨ ((j+1:ℕ):ℝ)/(2:ℝ)^s ≤ x) :
    periodizedDerivative ψ s j hj k (x:UnitAddCircle) = 0 := by
  rw [periodizedDerivative_unit_interval ψ s j hj k x hx,
    iteratedDeriv_dyadicLift]
  have hpow : 0 < (2:ℝ)^s := by positivity
  rcases hout with hleft | hright
  · have harg : (2:ℝ)^s*x-(j:ℝ) ≤ 0 := by
      rw [le_div_iff₀ hpow] at hleft
      nlinarith
    have hnot : (2:ℝ)^s*x-(j:ℝ) ∉ tsupport ψ.atom := by
      intro hh
      have ht := ψ.tsupport_subset hh
      linarith [ht.1]
    change (2:ℝ)^(s*k) * iteratedDeriv k ψ.atom ((2:ℝ)^s*x-(j:ℝ)) = 0
    rw [iteratedDeriv_eq_zero_of_not_tsupport ψ k hnot]
    simp
  · have harg : 1 ≤ (2:ℝ)^s*x-(j:ℝ) := by
      rw [div_le_iff₀ hpow] at hright
      push_cast at hright
      nlinarith
    have hnot : (2:ℝ)^s*x-(j:ℝ) ∉ tsupport ψ.atom := by
      intro hh
      have ht := ψ.tsupport_subset hh
      linarith [ht.2]
    change (2:ℝ)^(s*k) * iteratedDeriv k ψ.atom ((2:ℝ)^s*x-(j:ℝ)) = 0
    rw [iteratedDeriv_eq_zero_of_not_tsupport ψ k hnot]
    simp

abbrev GenericDyadicShapeCell {d : ℕ} (s : Fin d → ℕ) :=
  ∀ i : Fin d, Fin (2^(s i))

def genericShapeDerivativeAtom {d : ℕ} (ψ : SmoothCompactBump)
    (s k : Fin d → ℕ) (j : GenericDyadicShapeCell s)
    (x : UnitAddTorus (Fin d)) : ℝ :=
  ∏ i : Fin d, periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) (x i)

def genericFixedShapeSynthesis {d : ℕ} (ψ : SmoothCompactBump)
    (s : Fin d → ℕ) (c : GenericDyadicShapeCell s → ℝ) : RealPeriodic d where
  toFun x := ∑ j : GenericDyadicShapeCell s,
    c j * genericShapeDerivativeAtom ψ s (fun _ => 0) j x
  continuous_toFun := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0).continuous.comp
        (continuous_apply i))

def genericDerivativeSynthesis {d : ℕ} (ψ : SmoothCompactBump)
    (s k : Fin d → ℕ) (c : GenericDyadicShapeCell s → ℝ) : RealPeriodic d where
  toFun x := ∑ j : GenericDyadicShapeCell s,
    c j * genericShapeDerivativeAtom ψ s k j x
  continuous_toFun := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i)).continuous.comp
        (continuous_apply i))

theorem genericShapeDerivativeAtom_mul_eq_zero_of_ne {d : ℕ}
    (ψ : SmoothCompactBump) (s k : Fin d → ℕ)
    (j j' : GenericDyadicShapeCell s) (hjj : j ≠ j')
    (x : UnitAddTorus (Fin d)) :
    genericShapeDerivativeAtom ψ s k j x * genericShapeDerivativeAtom ψ s k j' x = 0 := by
  classical
  have hcoord : ∃ i : Fin d, j i ≠ j' i := by
    by_contra h
    push_neg at h
    exact hjj (funext h)
  obtain ⟨i, hji⟩ := hcoord
  have hval : (j i).val ≠ (j' i).val := by
    intro he
    exact hji (Fin.ext he)
  let y : Set.Ico (0:ℝ) (0+1) := AddCircle.equivIco 1 0 (x i)
  have hyx : (y.val : UnitAddCircle)=x i := by
    dsimp [y]
    simpa using (AddCircle.coe_equivIco (p:=(1:ℝ)) (a:=(0:ℝ)) (y:=x i))
  have hy : y.val ∈ Set.Ico (0:ℝ) 1 := by simpa using y.property
  have hzero :
      periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) (x i) = 0 ∨
      periodizedDerivative ψ (s i) (j' i).val (j' i).isLt (k i) (x i) = 0 := by
    have hordered (a b : ℕ) (ha : a < 2^(s i)) (hb : b < 2^(s i))
        (hab : a < b) :
        periodizedDerivative ψ (s i) a ha (k i) (x i) = 0 ∨
        periodizedDerivative ψ (s i) b hb (k i) (x i) = 0 := by
      by_cases hleft : y.val ≤ ((a+1:ℕ):ℝ)/(2:ℝ)^(s i)
      · have hcell : ((a+1:ℕ):ℝ) ≤ (b:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hab
        have hleft' : y.val ≤ (b:ℝ)/(2:ℝ)^(s i) :=
          le_trans hleft (div_le_div_of_nonneg_right hcell (by positivity))
        right
        rw [← hyx]
        exact periodizedDerivative_zero_of_outside_cell ψ (s i) b hb (k i)
          y.val hy (Or.inl hleft')
      · have hright : ((a+1:ℕ):ℝ)/(2:ℝ)^(s i) ≤ y.val := le_of_not_ge hleft
        left
        rw [← hyx]
        exact periodizedDerivative_zero_of_outside_cell ψ (s i) a ha (k i)
          y.val hy (Or.inr hright)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · exact hordered (j i).val (j' i).val (j i).isLt (j' i).isLt hlt
    · have h := hordered (j' i).val (j i).val (j' i).isLt (j i).isLt hgt
      exact Or.symm h
  rw [genericShapeDerivativeAtom, genericShapeDerivativeAtom,
    ← Finset.prod_mul_distrib]
  have hfactor :
      periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) (x i) *
        periodizedDerivative ψ (s i) (j' i).val (j' i).isLt (k i) (x i) = 0 := by
    rcases hzero with hz | hz
    · simp [hz]
    · simp [hz]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor

theorem genericShapeDerivativeAtom_abs_le {d : ℕ}
    (ψ : SmoothCompactBump) (s k : Fin d → ℕ)
    (j : GenericDyadicShapeCell s) (x : UnitAddTorus (Fin d))
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) ψ.atom y| ≤ C i) :
    |genericShapeDerivativeAtom ψ s k j x| ≤
      ∏ i : Fin d, (C i*(2:ℝ)^(s i*k i)) := by
  rw [genericShapeDerivativeAtom, Finset.abs_prod]
  apply prod_le_prod_nonneg_real (Finset.univ : Finset (Fin d))
  · intro i hi; exact abs_nonneg _
  · intro i hi; exact mul_nonneg (hC i) (by positivity)
  · intro i hi
    exact (periodizedDerivative_abs_le ψ (s i) (j i).val (j i).isLt
      (k i) (C i) (hderiv i) (x i))

theorem genericDerivativeSynthesis_abs_le_of_coeff_bound {d : ℕ}
    (ψ : SmoothCompactBump) (s k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) ψ.atom y| ≤ C i) :
    ∀ x : UnitAddTorus (Fin d),
      |genericDerivativeSynthesis ψ s k c x| ≤
        M * ∏ i : Fin d, (C i*(2:ℝ)^(s i*k i)) := by
  classical
  intro x
  let a : GenericDyadicShapeCell s → ℝ := fun j =>
    c j * genericShapeDerivativeAtom ψ s k j x
  have hpair (j j' : GenericDyadicShapeCell s) (hjj : j ≠ j') :
      a j*a j'=0 := by
    dsimp [a]
    rw [show (c j * genericShapeDerivativeAtom ψ s k j x) *
      (c j' * genericShapeDerivativeAtom ψ s k j' x) =
        (c j*c j')*(genericShapeDerivativeAtom ψ s k j x *
          genericShapeDerivativeAtom ψ s k j' x) by ring]
    rw [genericShapeDerivativeAtom_mul_eq_zero_of_ne ψ s k j j' hjj x]
    ring
  have hsum (j : GenericDyadicShapeCell s) (hj : a j ≠ 0) :
      (∑ j' : GenericDyadicShapeCell s, a j') = a j := by
    apply Finset.sum_eq_single j
    · intro j' hj' hneq
      by_contra hnonzero
      exact hj (by
        have hz := hpair j j' hneq.symm
        exact (mul_eq_zero.mp hz).resolve_right hnonzero)
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  by_cases hex : ∃ j : GenericDyadicShapeCell s, a j ≠ 0
  · obtain ⟨j,hj⟩ := hex
    rw [show genericDerivativeSynthesis ψ s k c x =
        ∑ j' : GenericDyadicShapeCell s, a j' by simp [genericDerivativeSynthesis,a]]
    rw [hsum j hj]
    calc
      |c j * genericShapeDerivativeAtom ψ s k j x| =
          |c j| * |genericShapeDerivativeAtom ψ s k j x| := by rw [abs_mul]
      _ ≤ M*∏ i : Fin d, (C i*(2:ℝ)^(s i*k i)) :=
        mul_le_mul (hcoeff j)
          (genericShapeDerivativeAtom_abs_le ψ s k j x C hC hderiv)
          (abs_nonneg _) hM
  · have hz : ∀ j : GenericDyadicShapeCell s, a j=0 := by
      intro j
      by_contra hne
      exact hex ⟨j,hne⟩
    rw [show genericDerivativeSynthesis ψ s k c x =
        ∑ j : GenericDyadicShapeCell s, a j by simp [genericDerivativeSynthesis,a]]
    change |∑ j : GenericDyadicShapeCell s, a j| ≤
      M * ∏ i : Fin d, (C i*(2:ℝ)^(s i*k i))
    calc
      |∑ j : GenericDyadicShapeCell s, a j| = 0 := by simp [hz]
      _ ≤ M*∏ i : Fin d, (C i*(2:ℝ)^(s i*k i)) := by
        apply mul_nonneg hM
        apply Finset.prod_nonneg
        intro i hi
        exact mul_nonneg (hC i) (by positivity)

theorem genericShapeDerivativeAtom_fourierCoeff_eq_prod {d : ℕ}
    (ψ : SmoothCompactBump) (s k : Fin d → ℕ)
    (j : GenericDyadicShapeCell s) (n : Fin d → ℤ) :
    realPeriodicFourierCoeff ⟨genericShapeDerivativeAtom ψ s k j, by
      change Continuous (fun x : UnitAddTorus (Fin d) =>
        ∏ i : Fin d, periodizedDerivative ψ (s i) (j i).val
          (j i).isLt (k i) (x i))
      exact continuous_finsetProd Finset.univ fun i hi =>
        (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i)).continuous.comp
          (continuous_apply i)⟩ n =
      ∏ i : Fin d, fourierCoeff
        (fun x : UnitAddCircle =>
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i) := by
  classical
  unfold realPeriodicFourierCoeff complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_mk]
  have hfun :
      (fun x : UnitAddTorus (Fin d) => UnitAddTorus.mFourier (-n) x •
        (genericShapeDerivativeAtom ψ s k j x : ℂ)) =
      fun x => ∏ i : Fin d,
        (fourier (-(n i)) (x i) •
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) (x i) : ℂ)) := by
    funext x
    simp [UnitAddTorus.mFourier, genericShapeDerivativeAtom,
      smul_eq_mul, Finset.prod_mul_distrib]
  rw [hfun]
  change (∫ x : (i : Fin d) → UnitAddCircle,
      ∏ i : Fin d, (fourier (-(n i)) (x i) •
        (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) (x i) : ℂ))
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i y => fourier (-(n i)) y •
      (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) y : ℂ))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [fourierCoeff, fourier, smul_eq_mul]

theorem genericDerivativeSynthesis_fourierCoeff_eq_sum {d : ℕ}
    (ψ : SmoothCompactBump) (s k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ) (n : Fin d → ℤ) :
    realPeriodicFourierCoeff (genericDerivativeSynthesis ψ s k c) n =
      ∑ j : GenericDyadicShapeCell s, (c j : ℂ) *
        ∏ i : Fin d, fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i) := by
  classical
  unfold realPeriodicFourierCoeff complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  change (∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) x •
      ((∑ j : GenericDyadicShapeCell s,
        c j * genericShapeDerivativeAtom ψ s k j x : ℝ) : ℂ)
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) = _
  have hfun :
      (fun x : UnitAddTorus (Fin d) => UnitAddTorus.mFourier (-n) x •
        ((∑ j : GenericDyadicShapeCell s,
          c j * genericShapeDerivativeAtom ψ s k j x : ℝ) : ℂ)) =
      fun x => ∑ j : GenericDyadicShapeCell s, (c j : ℂ) *
        (UnitAddTorus.mFourier (-n) x *
          (genericShapeDerivativeAtom ψ s k j x : ℂ)) := by
    funext x
    simp only [smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
    change (c j : ℂ) * realPeriodicFourierCoeff
      ⟨genericShapeDerivativeAtom ψ s k j, by
        change Continuous (fun x : UnitAddTorus (Fin d) =>
          ∏ i : Fin d, periodizedDerivative ψ (s i) (j i).val
            (j i).isLt (k i) (x i))
        exact continuous_finsetProd Finset.univ fun i hi =>
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i)).continuous.comp
            (continuous_apply i)⟩ n = _
    rw [genericShapeDerivativeAtom_fourierCoeff_eq_prod]
  · intro j hj
    have hc : Continuous (fun x : UnitAddTorus (Fin d) =>
        UnitAddTorus.mFourier (-n) x *
          (genericShapeDerivativeAtom ψ s k j x : ℂ)) := by
      exact (UnitAddTorus.mFourier (-n)).continuous.mul
        (Complex.continuous_ofReal.comp (continuous_finsetProd Finset.univ fun i hi =>
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i)).continuous.comp
            (continuous_apply i)))
    exact (continuous_const.mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem genericFixedShapeMixed_fourierCoeff_identity {d : ℕ}
    (ψ : SmoothCompactBump) (s t k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ) (n : Fin d → ℤ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i))) :
    tensorMultiplier t n * realPeriodicFourierCoeff (genericFixedShapeSynthesis ψ s c) n =
      fixedShapeMixedSymbol t k n *
        realPeriodicFourierCoeff (genericDerivativeSynthesis ψ s k c) n := by
  classical
  rw [genericDerivativeSynthesis_fourierCoeff_eq_sum]
  have hbase :
      realPeriodicFourierCoeff (genericFixedShapeSynthesis ψ s c) n =
        ∑ j : GenericDyadicShapeCell s, (c j : ℂ) *
          ∏ i : Fin d, fourierCoeff
            (fun x : UnitAddCircle =>
              (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i) := by
    simpa [genericFixedShapeSynthesis, genericDerivativeSynthesis,
      genericShapeDerivativeAtom] using
      (genericDerivativeSynthesis_fourierCoeff_eq_sum ψ s (fun _ => 0) c n)
  rw [hbase, tensorMultiplier, fixedShapeMixedSymbol]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoord (i : Fin d) :
      (scalarBlock (t i) (n i : ℝ) : ℂ) *
          fourierCoeff (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i) =
        (if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i)) *
          fourierCoeff (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i) := by
    rcases hscale i with hk | ⟨hti, hki_pos, hki⟩
    · simp [hk]
    · have hk0 : k i ≠ 0 := by omega
      by_cases hn : n i = 0
      · simp [hn, hk0, inverseMultiplier, scalarBlock_zero (t i) hti]
      · rw [periodizedDerivative_fourier_eq_pow ψ (s i) (j i).val
          (j i).isLt (k i) (n i) hn]
        simp only [if_neg hn, if_neg hk0]
        have hden : (2 * Real.pi * Complex.I * ((n i : ℤ) : ℂ)) ^ (k i) ≠ 0 := by
          apply pow_ne_zero
          apply mul_ne_zero
          · apply mul_ne_zero
            · norm_num [Real.pi_ne_zero]
            · exact Complex.I_ne_zero
          · exact_mod_cast hn
        simp only [inverseMultiplier, if_neg hn]
        field_simp [hden]
        <;> ring
  have hprod :
      ∏ i : Fin d, ((scalarBlock (t i) (n i : ℝ) : ℂ) *
        fourierCoeff (fun x : UnitAddCircle =>
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i)) =
      ∏ i : Fin d, ((if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
        else inverseMultiplier (t i) (k i) (n i)) *
        fourierCoeff (fun x : UnitAddCircle =>
          (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hcoord i
  calc
    ((∏ i : Fin d, scalarBlock (t i) (n i : ℝ) : ℝ) : ℂ) *
        ((c j : ℂ) * ∏ i : Fin d, fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i)) =
      (∏ i : Fin d, (scalarBlock (t i) (n i : ℝ) : ℂ)) *
        ((c j : ℂ) * ∏ i : Fin d, fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i)) := by
      simp only [Complex.ofReal_prod]
    _ = (c j : ℂ) * ∏ i : Fin d,
        ((scalarBlock (t i) (n i : ℝ) : ℂ) * fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i)) := by
      calc
        _ = (c j : ℂ) * ((∏ i : Fin d, (scalarBlock (t i) (n i : ℝ) : ℂ)) *
            ∏ i : Fin d, fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDerivative ψ (s i) (j i).val (j i).isLt 0 x : ℂ)) (n i)) := by ring
        _ = _ := by rw [← Finset.prod_mul_distrib]
    _ = (c j : ℂ) * ∏ i : Fin d,
        ((if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i)) * fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i)) := by
      rw [hprod]
    _ = (∏ i : Fin d,
        (if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i))) *
        ((c j : ℂ) * ∏ i : Fin d, fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDerivative ψ (s i) (j i).val (j i).isLt (k i) x : ℂ)) (n i)) := by
      rw [Finset.prod_mul_distrib]
      ring

private theorem generic_mFourier_sub_mul {d : ℕ} (n : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier n (x-y) =
      UnitAddTorus.mFourier n x * UnitAddTorus.mFourier (-n) y := by
  classical
  have hcoord : ∀ i : Fin d,
      fourier (n i) ((x-y) i) = fourier (n i) (x i) * fourier (-n i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem generic_mixed_term_integrable {d : ℕ}
    (ψ : SmoothCompactBump) (s t k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ) (n : Fin d → ℤ)
    (x : UnitAddTorus (Fin d)) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
        ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
      (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
        ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem genericFixedShapeBlock_eq_mixedKernel_integral {d : ℕ}
    (ψ : SmoothCompactBump) (s t k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (x : UnitAddTorus (Fin d)) :
    block t (genericFixedShapeSynthesis ψ s c) x =
      ∫ y : UnitAddTorus (Fin d),
        (∑ n ∈ frequencyBox t,
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  unfold block torusFourierPolynomial realPeriodicFourierCoeff
    complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul,
    Finset.sum_apply]
  calc
    _ = ∑ n ∈ frequencyBox t,
        (tensorMultiplier t n : ℂ) *
          UnitAddTorus.mFourierCoeff
            (complexifyRealPeriodic (genericFixedShapeSynthesis ψ s c)) n *
          UnitAddTorus.mFourier n x := by rfl
    _ = ∑ n ∈ frequencyBox t,
        fixedShapeMixedSymbol t k n *
          UnitAddTorus.mFourierCoeff
            (complexifyRealPeriodic (genericDerivativeSynthesis ψ s k c)) n *
          UnitAddTorus.mFourier n x := by
          apply Finset.sum_congr rfl
          intro n hn
          change (tensorMultiplier t n : ℂ) *
              realPeriodicFourierCoeff (genericFixedShapeSynthesis ψ s c) n *
              UnitAddTorus.mFourier n x =
            fixedShapeMixedSymbol t k n *
              realPeriodicFourierCoeff (genericDerivativeSynthesis ψ s k c) n *
              UnitAddTorus.mFourier n x
          rw [← genericFixedShapeMixed_fourierCoeff_identity ψ s t k c n hscale]
    _ = ∑ n ∈ frequencyBox t,
        ∫ y : UnitAddTorus (Fin d),
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hfun : (fun y : UnitAddTorus (Fin d) =>
                (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
                  ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)) =
              fun y => (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                (UnitAddTorus.mFourier (-n) y *
                  ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)) := by
                funext y
                rw [smul_eq_mul, generic_mFourier_sub_mul]
                ring
            rw [hfun]
            change fixedShapeMixedSymbol t k n *
                UnitAddTorus.mFourierCoeff
                  (complexifyRealPeriodic (genericDerivativeSynthesis ψ s k c)) n *
                UnitAddTorus.mFourier n x = _
            rw [UnitAddTorus.mFourierCoeff]
            simp only [complexifyRealPeriodic, smul_eq_mul]
            calc
              fixedShapeMixedSymbol t k n *
                  (∫ y : UnitAddTorus (Fin d),
                    UnitAddTorus.mFourier (-n) y *
                      ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) *
                  UnitAddTorus.mFourier n x =
                (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                  ∫ y : UnitAddTorus (Fin d),
                    UnitAddTorus.mFourier (-n) y *
                      ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by ring
              _ = ∫ y : UnitAddTorus (Fin d),
                  (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                    (UnitAddTorus.mFourier (-n) y *
                      ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ))
                  ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                    rw [integral_const_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        ∑ n ∈ frequencyBox t,
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
          symm
          apply integral_finsetSum
          intro n hn
          exact generic_mixed_term_integrable ψ s t k c n x

theorem genericFixedShapeBlock_pointwise_le_kernelL1_mul_derivativeSup
    {d : ℕ} (ψ : SmoothCompactBump) (s t k : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L)
    (hderiv : ∀ y : UnitAddTorus (Fin d),
      |genericDerivativeSynthesis ψ s k c y| ≤ U) :
    ∀ x : UnitAddTorus (Fin d),
      ‖block t (genericFixedShapeSynthesis ψ s c) x‖ ≤ L*U := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let K : C(UnitAddTorus (Fin d),ℂ) := coordinateProductKernel
    (fixedShapeMixedKernel t k)
  let u : C(UnitAddTorus (Fin d),ℂ) :=
    ⟨fun y => (genericDerivativeSynthesis ψ s k c y : ℝ),
      Complex.continuous_ofReal.comp (genericDerivativeSynthesis ψ s k c).continuous⟩
  have hkernelSum := fixedShapeMixedKernel_eq_sum t k hscale
  have hkernelAt (x y : UnitAddTorus (Fin d)) :
      (∑ n ∈ frequencyBox t,
        fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) = K (x-y) := by
    have hh := congrArg (fun f : C(UnitAddTorus (Fin d),ℂ) => f (x-y)) hkernelSum
    simpa [K, fixedShapeMixedSumKernel, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply] using hh.symm
  have hconv (x : UnitAddTorus (Fin d)) :
      block t (genericFixedShapeSynthesis ψ s c) x =
        ∫ y : UnitAddTorus (Fin d), K y*u (x-y) ∂μ := by
    rw [genericFixedShapeBlock_eq_mixedKernel_integral ψ s t k c hscale x]
    have hmp := BrownianSharp.AlignmentPaperTorusTranslation.sub_left_measurePreserving x
    let g : UnitAddTorus (Fin d) → ℂ := fun y => K y*u (x-y)
    calc
      (∫ y : UnitAddTorus (Fin d),
        ∑ n ∈ frequencyBox t,
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((genericDerivativeSynthesis ψ s k c y : ℝ) : ℂ) ∂μ) =
        ∫ y : UnitAddTorus (Fin d),
          (∑ n ∈ frequencyBox t,
            fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y))*u y ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              simp [u, Finset.sum_mul]
      _ = ∫ y : UnitAddTorus (Fin d), g (x-y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        change (∑ n ∈ frequencyBox t,
          fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y))*u y = g (x-y)
        rw [hkernelAt x y]
        simp [g,u,sub_sub_cancel]
      _ = ∫ y : UnitAddTorus (Fin d), g y ∂μ :=
        hmp.integral_comp (Homeomorph.subLeft x).measurableEmbedding g
      _ = ∫ y : UnitAddTorus (Fin d), K y*u (x-y) ∂μ := rfl
  intro x
  have hKint : Integrable (fun y : UnitAddTorus (Fin d) => ‖K y‖) μ := by
    apply Integrable.of_bound K.continuous.norm.aestronglyMeasurable ‖K‖
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using K.norm_coe_le_norm y
  have hint : Integrable (fun y : UnitAddTorus (Fin d) => K y*u (x-y)) μ := by
    apply Integrable.of_bound (K.continuous.mul
      (u.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (‖K‖*U)
    filter_upwards [] with y
    change ‖K y*u (x-y)‖ ≤ ‖K‖*U
    rw [norm_mul]
    have hu : ‖u (x-y)‖ ≤ U := by
      simpa [u, Complex.norm_real, Real.norm_eq_abs] using hderiv (x-y)
    calc
      ‖K y‖*‖u (x-y)‖ ≤ ‖K y‖*U := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ ≤ ‖K‖*U := mul_le_mul_of_nonneg_right (K.norm_coe_le_norm y) hU
  have hnorm := norm_integral_le_integral_norm (μ:=μ) (fun y => K y*u (x-y))
  have hk : (∫ y : UnitAddTorus (Fin d), ‖K y‖ ∂μ) ≤ L := by simpa [μ] using hkernel
  calc
    ‖block t (genericFixedShapeSynthesis ψ s c) x‖ =
        ‖∫ y : UnitAddTorus (Fin d), K y*u (x-y) ∂μ‖ := by rw [hconv x]
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y*u (x-y)‖ ∂μ := hnorm
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y‖*U ∂μ := by
      apply integral_mono_ae hint.norm (hKint.mul_const U)
      filter_upwards [] with y
      change ‖K y*u (x-y)‖ ≤ ‖K y‖*U
      rw [norm_mul]
      have hu : ‖u (x-y)‖ ≤ U := by
        simpa [u, Complex.norm_real, Real.norm_eq_abs] using hderiv (x-y)
      exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = (∫ y : UnitAddTorus (Fin d), ‖K y‖ ∂μ)*U := by rw [integral_mul_const]
    _ ≤ L*U := mul_le_mul_of_nonneg_right hk hU

def genericPeriodicAtom {d n : ℕ} (ψ : SmoothCompactBump)
    (a : LayerIndex d n) : RealPeriodic d where
  toFun x := ∏ i : Fin d,
    periodizedDerivative ψ (layerIndexDepth a i) (layerIndexCell a i)
      (layerIndexCell_lt a i) 0 (x i)
  continuous_toFun := continuous_finsetProd Finset.univ fun i hi =>
    (periodizedDerivative ψ (layerIndexDepth a i) (layerIndexCell a i)
      (layerIndexCell_lt a i) 0).continuous.comp (continuous_apply i)

def genericPeriodicSynthesisLinear {d n : ℕ} (ψ : SmoothCompactBump) :
    (LayerIndex d n → ℝ) →ₗ[ℝ] RealPeriodic d where
  toFun x := ∑ a, x a • genericPeriodicAtom ψ a
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul, mul_comm]

theorem genericPeriodicAtom_eq_genericShapeAtom {d n : ℕ}
    (ψ : SmoothCompactBump) (r : Shape d n)
    (j : GenericDyadicShapeCell r.1) :
    genericPeriodicAtom ψ (⟨r,j⟩ : LayerIndex d n) =
      ⟨genericShapeDerivativeAtom ψ r.1 (fun _ => 0) j, by
        exact continuous_finsetProd Finset.univ fun i hi =>
          (periodizedDerivative ψ (r.1 i) (j i).val (j i).isLt 0).continuous.comp
            (continuous_apply i)⟩ := by
  apply ContinuousMap.ext
  intro x
  change (∏ i : Fin d, periodizedDerivative ψ (layerIndexDepth ⟨r,j⟩ i)
      (layerIndexCell ⟨r,j⟩ i) (layerIndexCell_lt ⟨r,j⟩ i) 0 (x i)) =
    ∏ i : Fin d, periodizedDerivative ψ (r.1 i) (j i).val (j i).isLt 0 (x i)
  rfl

theorem genericPeriodicSynthesis_eq_sum_shapes {d n : ℕ}
    (ψ : SmoothCompactBump) (x : LayerIndex d n → ℝ) :
    genericPeriodicSynthesisLinear ψ x =
      ∑ r : Shape d n,
        genericFixedShapeSynthesis ψ r.1 (fun j => x ⟨r,j⟩) := by
  classical
  apply ContinuousMap.ext
  intro z
  change (∑ a : LayerIndex d n, x a • genericPeriodicAtom ψ a) z =
    (∑ r : Shape d n, genericFixedShapeSynthesis ψ r.1
      (fun j => x ⟨r,j⟩)) z
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  rw [genericPeriodicAtom_eq_genericShapeAtom]
  rfl

theorem genericPeriodicSynthesis_weightedBlockNorm_top_le_sum_shapes
    {d n : ℕ} (ψ : SmoothCompactBump) (r : ℝ)
    (t : Fin d → ℕ) (x : LayerIndex d n → ℝ) :
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
      (genericPeriodicSynthesisLinear ψ x) ≤
      ∑ a : Shape d n, SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) := by
  classical
  have hdecomp (z : UnitAddTorus (Fin d)) :
      SmoothResolution.block t (genericPeriodicSynthesisLinear ψ x) z =
        ∑ a : Shape d n, SmoothResolution.block t
          (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z := by
    rw [genericPeriodicSynthesis_eq_sum_shapes]
    change smoothBlockLinear t
        (∑ a : Shape d n,
          genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z =
      ∑ a : Shape d n, smoothBlockLinear t
        (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z
    rw [map_sum]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  unfold SmoothResolution.weightedBlockNorm
  rw [show (fun z : UnitAddTorus (Fin d) =>
      SmoothResolution.block t (genericPeriodicSynthesisLinear ψ x) z) =
      (fun z => ∑ a : Shape d n, SmoothResolution.block t
        (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z) from by
          funext z; exact hdecomp z]
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))) *
        ∑ a : Shape d n, eLpNorm
          (fun z => SmoothResolution.block t
            (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z)
          (⊤:ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
      have htri := MeasureTheory.eLpNorm_sum_le
        (μ := (volume : Measure (UnitAddTorus (Fin d))))
        (p := (⊤:ℝ≥0∞))
        (f := fun a : Shape d n => fun z : UnitAddTorus (Fin d) =>
          SmoothResolution.block t
            (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z)
        (s := (Finset.univ : Finset (Shape d n))) (by simp)
      have hsumfun :
          (∑ a : Shape d n, fun z : UnitAddTorus (Fin d) =>
            SmoothResolution.block t
              (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z) =
          (fun z => ∑ a : Shape d n, SmoothResolution.block t
            (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z) := by
        funext z; simp
      have htri' : eLpNorm
          (fun z : UnitAddTorus (Fin d) => ∑ a : Shape d n,
            SmoothResolution.block t
              (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z)
          (⊤:ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) ≤
          ∑ a : Shape d n, eLpNorm
            (fun z => SmoothResolution.block t
              (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z)
            (⊤:ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
        rw [← hsumfun]
        exact htri
      exact mul_le_mul_of_nonneg_left htri' (by positivity)
    _ = ∑ a : Shape d n, ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))) *
          eLpNorm
            (fun z => SmoothResolution.block t
              (genericFixedShapeSynthesis ψ a.1 (fun j => x ⟨a,j⟩)) z)
            (⊤:ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) := by
      rw [Finset.mul_sum]

theorem genericFixedShape_weightedBlockNorm_top_le_endpointProfile
    {d n : ℕ} (ψ : SmoothCompactBump) (s : Fin d → ℕ)
    (hsum : ∑ i : Fin d, s i = n) (t : Fin d → ℕ)
    (c : GenericDyadicShapeCell s → ℝ) (M r Lscalar Lprofile Czero CK : ℝ)
    (K : ℕ) (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (hr : 0 ≤ r) (hK : Even K) (hKpos : 0 < K) (hrK : r < K)
    (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hC0 : 0 ≤ Czero) (hCK : 0 ≤ CK)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ q : ℕ, 0 < q →
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel q K x‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖*Lprofile)
    (hderiv0 : ∀ y, |iteratedDeriv 0 ψ.atom y| ≤ Czero)
    (hderivK : ∀ y, |iteratedDeriv K ψ.atom y| ≤ CK) :
    SmoothResolution.weightedBlockNorm (⊤:ℝ≥0∞) r t
      (genericFixedShapeSynthesis ψ s c) ≤
      ENNReal.ofReal (M*(max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) *
      nativeNikolskyShapeWeight t
        (ENNReal.ofReal ((2:ℝ)^(-r)))
        (ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r)))) s := by
  classical
  let k : Fin d → ℕ := fun i => if s i < t i then K else 0
  let C : Fin d → ℝ := fun i => if s i < t i then CK else Czero
  let H : Fin d → ℝ := fun i =>
    if s i < t i then Lprofile*((2:ℝ)^(t i))⁻¹ ^ K else Lscalar
  let U : ℝ := M*∏ i : Fin d, (C i*(2:ℝ)^(s i*k i))
  have hCnonneg : ∀ i, 0 ≤ C i := by
    intro i
    simp [C]
    split_ifs <;> assumption
  have hderiv : ∀ i y, |iteratedDeriv (k i) ψ.atom y| ≤ C i := by
    intro i y
    simp only [k,C]
    split_ifs with hit
    · exact hderivK y
    · exact hderiv0 y
  have hscale : ∀ i, k i=0 ∨ (0<t i ∧ 0<k i ∧ Even (k i)) := by
    intro i
    simp only [k]
    split_ifs with hit
    · right
      exact ⟨by omega, hKpos, hK⟩
    · exact Or.inl rfl
  have hHnonneg : ∀ i, 0 ≤ H i := by
    intro i
    simp [H]
    split_ifs <;> positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    apply mul_nonneg hM
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (hCnonneg i) (by positivity)
  have hkernel0 := fixedShapeMixedKernel_integral_le t k Lscalar hLs hscalar
    H hHnonneg (by
      intro i hk
      have hit : s i < t i := by
        by_contra hnot
        simp [k, hnot] at hk
      have ht : 0 < t i := Nat.zero_lt_of_lt hit
      have hInv := inverseProfileScale_norm_le_dyadic (t i) K
      have hprof := hprofile (t i) ht
      have hscaled : ‖inverseProfileScale (t i) K‖ * Lprofile ≤
          Lprofile * (((2:ℝ)^(t i))⁻¹ ^ K) := by
        calc
          _ = Lprofile * ‖inverseProfileScale (t i) K‖ := by ring
          _ ≤ Lprofile * (((2:ℝ)^(t i))⁻¹ ^ K) :=
            mul_le_mul_of_nonneg_left hInv hLp
      have hgoal := le_trans hprof hscaled
      exact ⟨ht, by simpa [k, hit] using hK,
        by simpa [H, k, hit] using hgoal⟩)
  have hR : (∏ i : Fin d, if k i = 0 then Lscalar else H i) = ∏ i, H i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hit : s i < t i
    · have hKzero : K ≠ 0 := by omega
      simp [k, H, hit, hKzero]
    · simp [k, H, hit]
  have hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ ∏ i, H i := by
    rw [← hR]
    exact hkernel0
  have hpoint := genericFixedShapeBlock_pointwise_le_kernelL1_mul_derivativeSup
    ψ s t k c hscale (∏ i, H i) U (Finset.prod_nonneg fun i hi => hHnonneg i) hU hkernel
    (genericDerivativeSynthesis_abs_le_of_coeff_bound ψ s k c M hM hcoeff C
      hCnonneg hderiv)
  have hraw : SmoothResolution.weightedBlockNorm (⊤:ℝ≥0∞) r t
      (genericFixedShapeSynthesis ψ s c) ≤
      ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))*((∏ i,H i)*U)) := by
    convert weightedBlockNorm_top_le_of_pointwise_bound r t
      (genericFixedShapeSynthesis ψ s c) ((∏ i,H i)*U)
      (mul_nonneg (Finset.prod_nonneg fun i hi => hHnonneg i) hU) hpoint using 1
  have hfactor := endpoint_product_profile_factor s t M r Lscalar Lprofile
    Czero CK K hM hr hK hKpos hrK hLs hLp hC0 hCK hsum
  have hraw' :
      (2:ℝ)^(r*∑ i,(t i:ℝ))*((∏ i,H i)*U) ≤
       M*(max (Lscalar*Czero) (Lprofile*CK))^d*(2:ℝ)^(r*(n:ℝ))*
        endpointNikolskyShapeWeightReal s t r K := by
    calc
      _ = (2:ℝ)^(r*∑ i,(t i:ℝ)) *
          (M * ∏ i, (H i * (C i * (2:ℝ)^(s i*k i)))) := by
            dsimp [U]
            conv_rhs => rw [Finset.prod_mul_distrib]
            ring_nf
      _ ≤ _ := by simpa [H, C, k] using hfactor
  have hB : 0≤M*(max (Lscalar*Czero) (Lprofile*CK))^d*(2:ℝ)^(r*(n:ℝ)) := by positivity
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))*((∏ i,H i)*U)) := hraw
    _ ≤ ENNReal.ofReal (M*(max (Lscalar*Czero) (Lprofile*CK))^d*
        (2:ℝ)^(r*(n:ℝ))*endpointNikolskyShapeWeightReal s t r K) :=
          ENNReal.ofReal_le_ofReal hraw'
    _ = ENNReal.ofReal (M*(max (Lscalar*Czero) (Lprofile*CK))^d*
          (2:ℝ)^(r*(n:ℝ))) * ENNReal.ofReal (endpointNikolskyShapeWeightReal s t r K) := by
          rw [ENNReal.ofReal_mul hB]
    _ = _ := by rw [← endpoint_profileENNReal_eq_native s t r K]

/-- Aggregate an actual per-shape profile for the generic periodized bump
through the established discrete weighted Young estimate. -/
theorem genericPeriodicBesov_of_shapeProfile
    {d n : ℕ} (ψ : SmoothCompactBump) (x : LayerIndex d n → ℝ)
    (r : ℝ) (theta : ℝ≥0∞) (B A qlow qhigh : ℝ≥0∞)
    (hθ : 1 ≤ theta) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hrow : ∀ t : Fin d → ℕ,
      (∑ s : Shape d n,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A)
    (hcol : ∀ s : Shape d n,
      (∑' t : Fin d → ℕ,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A)
    (hshape : ∀ s : Shape d n, ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (genericFixedShapeSynthesis ψ s.1 (fun j => x ⟨s,j⟩)) ≤
      B * nativeNikolskyShapeWeight t qlow qhigh s.1)
    (hbudgetNorm : if theta = ⊤ then B*A ≤ 1 else
      B ^ theta.toReal * A ^ theta.toReal * Fintype.card (Shape d n) ≤ 1) :
    SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
      (genericPeriodicSynthesisLinear ψ x) := by
  classical
  let envelope : (Fin d → ℕ) → ℝ≥0∞ := fun t =>
    B * ∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh s.1
  have hblock (t : Fin d → ℕ) :
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (genericPeriodicSynthesisLinear ψ x) ≤ envelope t := by
    calc
      _ ≤ ∑ s : Shape d n,
          SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
            (genericFixedShapeSynthesis ψ s.1 (fun j => x ⟨s,j⟩)) :=
          genericPeriodicSynthesis_weightedBlockNorm_top_le_sum_shapes ψ r t x
      _ ≤ ∑ s : Shape d n,
          B * nativeNikolskyShapeWeight t qlow qhigh s.1 :=
          Finset.sum_le_sum fun s hs => hshape s t
      _ = envelope t := by simp [envelope, Finset.mul_sum]
  have hbudget : if theta = ⊤ then (∀ t, envelope t ≤ 1) else
      ∑' t : Fin d → ℕ, (envelope t) ^ theta.toReal ≤ 1 := by
    by_cases htop : theta = ⊤
    · simp only [htop, ↓reduceIte]
      have hBtop : B*A ≤ 1 := by simpa [htop] using hbudgetNorm
      intro t
      calc
        envelope t ≤ B*A := by
          dsimp [envelope]
          exact mul_le_mul_of_nonneg_left (hrow t) bot_le
        _ ≤ 1 := hBtop
    · simp only [htop, ↓reduceIte]
      have hBfinite : B ^ theta.toReal * A ^ theta.toReal *
          Fintype.card (Shape d n) ≤ 1 := by simpa [htop] using hbudgetNorm
      have hp : 1 ≤ theta.toReal := by
        have hne : theta ≠ ⊤ := htop
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hne).2 hθ
      calc
        _ ≤ B ^ theta.toReal * A ^ theta.toReal *
            Fintype.card (Shape d n) := by
          change (∑' t : Fin d → ℕ,
            (B * ∑ s : Shape d n,
              nativeNikolskyShapeWeight t qlow qhigh s.1)^theta.toReal) ≤ _
          exact endpoint_discrete_weighted_young_unit
              (S := Shape d n) (T := Fin d → ℕ)
              (fun s t => nativeNikolskyShapeWeight t qlow qhigh s.1)
              A B (p := theta.toReal) hp hA0 hAtop hrow hcol
        _ ≤ 1 := hBfinite
  exact besovUnitBall_of_weightedBlockNorm_le_envelope
    (⊤ : ℝ≥0∞) r theta (genericPeriodicSynthesisLinear ψ x) hθ
    envelope hbudget hblock

/-- Generic compactly supported smooth bumps satisfy the same deterministic
all-theta endpoint estimate as the fixed atom. The proof uses the actual
periodized bump and its derivative envelopes. -/
theorem genericPeriodicBesov_of_boundedCoefficients
    {d n : ℕ} (ψ : SmoothCompactBump) (x : LayerIndex d n → ℝ)
    (M r : ℝ) (theta : ℝ≥0∞) (K : ℕ)
    (Lscalar Lprofile Czero CK : ℝ)
    (hM : 0 ≤ M) (hcoeff : ∀ j, |x j| ≤ M)
    (hr : 0 < r) (hK : Even K) (hKpos : 0 < K) (hrK : r < K)
    (hθ : 1 ≤ theta)
    (hLs : 0 ≤ Lscalar) (hLp : 0 ≤ Lprofile)
    (hC0 : 0 ≤ Czero) (hCK : 0 ≤ CK)
    (hscalar : ∀ q : ℕ,
      (∫ z : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q z‖
        ∂AddCircle.haarAddCircle) ≤ Lscalar)
    (hprofile : ∀ q : ℕ, 0 < q →
      (∫ z : UnitAddCircle, ‖inverseMultiplierKernel q K z‖
        ∂AddCircle.haarAddCircle) ≤ ‖inverseProfileScale q K‖ * Lprofile)
    (hderiv0 : ∀ y : ℝ, |iteratedDeriv 0 ψ.atom y| ≤ Czero)
    (hderivK : ∀ y : ℝ, |iteratedDeriv K ψ.atom y| ≤ CK)
    (hbudget : if theta = ⊤ then ENNReal.ofReal
      (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) *
        (((1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
          ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))) *
            (1-ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))))⁻¹)^d) ≤ 1
      else ENNReal.ofReal (M * (max (Lscalar*Czero) (Lprofile*CK))^d *
        (2:ℝ)^(r*(n:ℝ))) ^ theta.toReal *
      (((1 - ENNReal.ofReal ((2:ℝ)^(-r)))⁻¹ +
          ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))) *
            (1-ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r))))⁻¹)^d) ^ theta.toReal *
        Fintype.card (Shape d n) ≤ 1) :
    SmoothResolution.BesovUnitBall (⊤ : ℝ≥0∞) r theta
      (genericPeriodicSynthesisLinear ψ x) := by
  classical
  let qlow : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(-r))
  let qhigh : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(-((K:ℝ)-r)))
  let A : ℝ≥0∞ := ((1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹)^d
  let B : ℝ≥0∞ := ENNReal.ofReal
    (M * (max (Lscalar*Czero) (Lprofile*CK))^d * (2:ℝ)^(r*(n:ℝ)))
  have hrK' : (r:ℝ) < (K:ℝ) := by exact_mod_cast hrK
  have hq : qlow < 1 ∧ qhigh < 1 := by
    simpa [qlow, qhigh] using ennreal_dyadic_profile_bases_lt_one hr hrK'
  have hA0 : A ≠ 0 := by
    have hpos : 0 < (1-qlow)⁻¹ + qhigh*(1-qhigh)⁻¹ := by
      have hfinite : 1-qlow ≠ ⊤ := by finiteness
      have hinv : 0 < (1-qlow)⁻¹ := ENNReal.inv_pos.mpr hfinite
      exact lt_of_lt_of_le hinv (le_add_of_nonneg_right (by positivity))
    dsimp [A]
    exact pow_ne_zero _ (ne_of_gt hpos)
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    have hlowden : 1-qlow ≠ 0 := ne_of_gt (tsub_pos_of_lt hq.1)
    have hhighden : 1-qhigh ≠ 0 := ne_of_gt (tsub_pos_of_lt hq.2)
    finiteness
  have hrow : ∀ t : Fin d → ℕ,
      (∑ s : Shape d n, nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A := by
    intro t
    have h := endpoint_shape_profile_row_sum_le (n := n) t qlow qhigh hq.1 hq.2
    simpa [A] using h
  have hcol : ∀ s : Shape d n,
      (∑' t : Fin d → ℕ,
        nativeNikolskyShapeWeight t qlow qhigh s.1) ≤ A := by
    intro s
    have h := endpoint_shape_profile_column_sum_le s.1 qlow qhigh hq.1 hq.2
    simpa [A] using h
  have hshape : ∀ s : Shape d n, ∀ t : Fin d → ℕ,
      SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
        (genericFixedShapeSynthesis ψ s.1
          (fun j => x ⟨s,j⟩)) ≤
        B * nativeNikolskyShapeWeight t qlow qhigh s.1 := by
    intro s t
    have hsum : ∑ i : Fin d, s.1 i = n := by
      have hh := (Finset.mem_finsuppAntidiag'.mp s.2).1
      simpa [Finsupp.sum_fintype] using hh
    have hcoeff' : ∀ j : GenericDyadicShapeCell s.1, |x ⟨s,j⟩| ≤ M :=
      fun j => hcoeff ⟨s,j⟩
    simpa [B, qlow, qhigh] using
      (genericFixedShape_weightedBlockNorm_top_le_endpointProfile
        ψ s.1 hsum t (fun j => x ⟨s,j⟩) M r Lscalar Lprofile Czero CK K
        hM hcoeff' hr.le hK hKpos hrK hLs hLp hC0 hCK
        hscalar hprofile hderiv0 hderivK)
  have hbudgetNorm : if theta = ⊤ then B*A ≤ 1 else
      B ^ theta.toReal * A ^ theta.toReal * Fintype.card (Shape d n) ≤ 1 := by
    simpa [A, B, qlow, qhigh] using hbudget
  exact genericPeriodicBesov_of_shapeProfile ψ x r theta B A qlow qhigh
    hθ hA0 hAtop hrow hcol hshape hbudgetNorm

end BrownianSharp.AlignmentPaperGenericSmoothBumpBesov
