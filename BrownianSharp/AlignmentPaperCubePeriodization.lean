import BrownianSharp.TorusFoundations
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual continuous periodization of a cutoff function. A closed fundamental
cube is mapped onto the torus, and vanishing boundary values make the descent
well defined and continuous. The Matérn cutoff is supported strictly inside
this fundamental cube after the fixed period-eight rescaling. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp.AlignmentPaperCubePeriodization

/-- Closed fundamental cube for the unit torus. -/
abbrev FundamentalCube (d : ℕ) :=
  Set.Icc (fun _ : Fin d => (-(1:ℝ)/2)) (fun _ : Fin d => (1:ℝ)/2)

instance fundamentalCube_compact (d : ℕ) : CompactSpace (FundamentalCube d) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- The genuine quotient map from the closed cube to the product torus. -/
def cubeToTorus (d : ℕ) : C(FundamentalCube d, UnitAddTorus (Fin d)) where
  toFun := fun x i => (x.val i : UnitAddCircle)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' 1).comp
      ((continuous_apply i).comp continuous_subtype_val)

theorem cubeToTorus_surjective (d : ℕ) : Function.Surjective (cubeToTorus d) := by
  intro z
  let x : Fin d → ℝ := fun i => (AddCircle.equivIco 1 (-(1:ℝ)/2) (z i)).val
  have hx : x ∈ Set.Icc (fun _ => (-(1:ℝ)/2)) (fun _ => (1:ℝ)/2) := by
    constructor
    · intro i
      exact (AddCircle.equivIco 1 (-(1:ℝ)/2) (z i)).property.1
    · intro i
      have h := (AddCircle.equivIco 1 (-(1:ℝ)/2) (z i)).property.2
      dsimp [x]
      linarith
  refine ⟨⟨x,hx⟩,?_⟩
  funext i
  exact AddCircle.coe_equivIco

theorem cubeToTorus_isQuotientMap (d : ℕ) : Topology.IsQuotientMap (cubeToTorus d) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (cubeToTorus_surjective d) (cubeToTorus d).continuous

private theorem coe_eq_implies_eq_of_interior {x y : ℝ}
    (hx : x ∈ Set.Ioo (-(1:ℝ)/2) ((1:ℝ)/2))
    (hy : y ∈ Set.Icc (-(1:ℝ)/2) ((1:ℝ)/2))
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) : x=y := by
  rcases hx with ⟨hxl,hxu⟩
  rcases hy with ⟨hyl,hyu⟩
  by_cases hyt : y < (1:ℝ)/2
  · apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1:ℝ)) (a := -(1:ℝ)/2) (by constructor <;> linarith)
      (by constructor <;> linarith)).mp hxy
  · have hyeq : y = (1:ℝ)/2 := by linarith
    subst y
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := (1:ℝ)) (a := -(1:ℝ)/2) (by constructor <;> linarith)
      (by constructor <;> norm_num)).mp hxy

variable {E : Type*} [TopologicalSpace E] [Zero E]

abbrev VanishesOnBoundary {d : ℕ} (f : C(FundamentalCube d,E)) : Prop :=
  ∀ x, (∃ i, x.val i = -(1:ℝ)/2 ∨ x.val i = (1:ℝ)/2) → f x=0

private theorem nonzero_interior {d : ℕ} (f : C(FundamentalCube d,E))
    (hf : VanishesOnBoundary f) (x : FundamentalCube d) (hx : f x ≠ 0) (i : Fin d) :
    x.val i ∈ Set.Ioo (-(1:ℝ)/2) ((1:ℝ)/2) := by
  have hlo : x.val i ≠ -(1:ℝ)/2 := by intro h; exact hx (hf x ⟨i,Or.inl h⟩)
  have hhi : x.val i ≠ (1:ℝ)/2 := by intro h; exact hx (hf x ⟨i,Or.inr h⟩)
  exact ⟨lt_of_le_of_ne (x.property.1 i) hlo.symm,
    lt_of_le_of_ne (x.property.2 i) hhi⟩

theorem boundary_vanishing_constant_on_fibers {d : ℕ}
    (f : C(FundamentalCube d,E)) (hf : VanishesOnBoundary f)
    (x y : FundamentalCube d) (hxy : cubeToTorus d x = cubeToTorus d y) : f x=f y := by
  have heq (x y : FundamentalCube d) (hx : f x ≠ 0)
      (hxy : cubeToTorus d x = cubeToTorus d y) : x=y := by
    apply Subtype.ext
    funext i
    apply coe_eq_implies_eq_of_interior (nonzero_interior f hf x hx i)
      ⟨y.property.1 i,y.property.2 i⟩
    exact congrFun hxy i
  by_cases hx : f x=0
  · by_cases hy : f y=0
    · rw [hx,hy]
    · rw [heq y x hy hxy.symm]
  · rw [heq x y hx hxy]

/-- The concrete continuous torus extension of a function which vanishes on
the boundary of its fundamental cube. -/
def periodizeCube {d : ℕ} (f : C(FundamentalCube d,E))
    (hf : VanishesOnBoundary f) : C(UnitAddTorus (Fin d),E) :=
  (cubeToTorus_isQuotientMap d).lift f
    (boundary_vanishing_constant_on_fibers f hf)

@[simp] theorem periodizeCube_cubeToTorus {d : ℕ}
    (f : C(FundamentalCube d,E)) (hf : VanishesOnBoundary f) (x : FundamentalCube d) :
    periodizeCube f hf (cubeToTorus d x)=f x := by
  exact congrArg (fun g : C(FundamentalCube d,E) => g x)
    ((cubeToTorus_isQuotientMap d).lift_comp f
      (boundary_vanishing_constant_on_fibers f hf))

/-- Fixed rescaling from period eight to period one. -/
def periodEightRescale {d : ℕ} (f : C((Fin d → ℝ),E)) : C(FundamentalCube d,E) :=
  ⟨fun x => f (fun i => 8*x.val i), f.continuous.comp
    (continuous_pi (fun i => continuous_const.mul
      ((continuous_apply i).comp continuous_subtype_val)))⟩

/-- A function supported in the inner cube descends after period-eight
rescaling, because opposite boundary faces both have value zero. -/
def periodizePeriodEight {d : ℕ} (f : C((Fin d → ℝ),E))
    (hf : ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) → f x=0) :
    C(UnitAddTorus (Fin d),E) :=
  periodizeCube (periodEightRescale f) (by
    intro x hx
    obtain ⟨i,hi⟩ := hx
    apply hf
    refine ⟨i,?_⟩
    rcases hi with hi|hi
    · left; change 8*x.val i ≤ -2; linarith
    · right; change 2 ≤ 8*x.val i; linarith)

/-- The original cube sits strictly inside the larger torus. -/
def cubeIntoPeriodEightTorus {d : ℕ} (t : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun i => ((t i/8 : ℝ) : UnitAddCircle)

/-- Exact preservation of the original function on [0,1]^d by the actual
continuous periodized extension. -/
theorem periodizePeriodEight_restrict {d : ℕ} (f : C((Fin d → ℝ),E))
    (hf : ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) → f x=0)
    (t : Fin d → ℝ) (ht : t ∈ Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) :
    periodizePeriodEight f hf (cubeIntoPeriodEightTorus t)=f t := by
  let x : FundamentalCube d := ⟨fun i => t i/8, by
    constructor
    · intro i; have h := ht.1 i; linarith
    · intro i; have h := ht.2 i; linarith⟩
  change periodizeCube (periodEightRescale f) _ (cubeToTorus d x)=f t
  rw [periodizeCube_cubeToTorus]
  change f (fun i => 8*(t i/8))=f t
  congr 1
  funext i
  ring

/-- Recovery on every representative of the closed fundamental cube, useful
for computing the actual Fourier coefficients with the correct 8^-d factor. -/
theorem periodizePeriodEight_on_fundamentalCube {d : ℕ} (f : C((Fin d → ℝ),E))
    (hf : ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) → f x=0)
    (t : FundamentalCube d) :
    periodizePeriodEight f hf (cubeToTorus d t)=f (fun i => 8*t.val i) := by
  exact periodizeCube_cubeToTorus _ _ t

/-- Fourier coefficients of the actual periodized extension, with the exact
period-eight normalization. This follows from the torus fundamental-domain
integral and the Haar change of variables, not from a presumed coefficient
representation. -/
theorem periodizePeriodEight_fourierCoeff {d : ℕ}
    (f : C((Fin d → ℝ),ℂ))
    (hf : ∀ x, (∃ i, x i ≤ -2 ∨ 2 ≤ x i) → f x=0) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodizePeriodEight f hf) k =
      ((8:ℝ)^d)⁻¹ • ∫ t : Fin d → ℝ,
        UnitAddTorus.mFourier (-k) (cubeIntoPeriodEightTorus t) * f t := by
  let D : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (-(1:ℝ)/2) (-(1:ℝ)/2+1)}
  let H : (Fin d → ℝ) → ℂ := fun t =>
    UnitAddTorus.mFourier (-k) (cubeIntoPeriodEightTorus t) * f t
  have hD : MeasurableSet D := by
    have hm := MeasurableSet.iInter (fun i : Fin d =>
      (measurableSet_Ioc (a := -(1:ℝ)/2) (b := -(1:ℝ)/2+1)).preimage
        (measurable_pi_apply i))
    convert hm using 1
    ext x
    simp [D]
  have hchar (x : Fin d → ℝ) :
      cubeIntoPeriodEightTorus ((8:ℝ) • x) = fun i => (x i : UnitAddCircle) := by
    funext i
    change (((8*x i)/8:ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
    congr 1
    ring
  have hzero (x : Fin d → ℝ) (hx : x ∉ D) : H ((8:ℝ) • x)=0 := by
    have hnot : ¬ ∀ i, x i ∈ Set.Ioc (-(1:ℝ)/2) (-(1:ℝ)/2+1) := hx
    push Not at hnot
    obtain ⟨i,hi⟩ := hnot
    have hfzero : f ((8:ℝ) • x)=0 := by
      apply hf
      refine ⟨i,?_⟩
      by_cases hlo : x i ≤ -(1:ℝ)/2
      · left; change 8*x i ≤ -2; linarith
      · right
        have hhi : -(1:ℝ)/2+1 < x i := by
          simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hi
          rcases hi with hi|hi
          · contradiction
          · exact hi
        change 2 ≤ 8*x i
        linarith
    simp [H,hfzero]
  calc
    UnitAddTorus.mFourierCoeff (periodizePeriodEight f hf) k =
      ∫ x in D, UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
        periodizePeriodEight f hf (fun i => (x i : UnitAddCircle)) :=
      UnitAddTorus.mFourierCoeff_eq_integral _ k (fun _ => -(1:ℝ)/2)
    _ = ∫ x in D, H ((8:ℝ) • x) := by
      apply setIntegral_congr_fun hD
      intro x hx
      have hxc : x ∈ Set.Icc (fun _ => -(1:ℝ)/2) (fun _ => (1:ℝ)/2) := by
        constructor
        · intro i; exact (hx i).1.le
        · intro i; have h := (hx i).2; linarith
      have hp := periodizePeriodEight_on_fundamentalCube f hf ⟨x,hxc⟩
      change periodizePeriodEight f hf (fun i => (x i : UnitAddCircle)) =
        f ((8:ℝ) • x) at hp
      simp only [H,hchar,hp,smul_eq_mul]
    _ = ∫ x, H ((8:ℝ) • x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = ((8:ℝ)^d)⁻¹ • ∫ x, H x := by
      simpa using MeasureTheory.Measure.integral_comp_smul
        (volume : MeasureTheory.Measure (Fin d → ℝ)) H 8

end BrownianSharp.AlignmentPaperCubePeriodization
