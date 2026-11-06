import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.AlignmentFractionalDensity
import BrownianSharp.BrownianSheetOnCube

/-! Common integer-order integration is identified with iterated ordinary
Riemann--Liouville operators.  This packages the actual Volterra/Fubini
recurrence used to obtain the Gamma-normalized kernels. -/

noncomputable section
open MeasureTheory
open HaarQuarter

namespace BrownianSharp.AlignmentPaperIntegratedSemigroup

open BrownianSharp.AlignmentGaussianBochner
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentGaussianRates

/-- Restrict a cube path to one coordinate line, extending it by clamping
outside the cube. -/
def coordinateLineProfile {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) (x : BrownianCubeAnchor d) :
    C(UnitInterval, ℝ) :=
  ⟨fun u => brownianCubeGlobalExtension f (Function.update x.val i u.val), by
    exact (brownianCubeGlobalExtension f).continuous.comp (by fun_prop)⟩

/-- The coordinate-line profiles vary continuously with the remaining cube
anchor. -/
def coordinateLineProfileFamily {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) :
    C(BrownianCubeAnchor d, C(UnitInterval, ℝ)) where
  toFun := coordinateLineProfile i f
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ (by
    exact (brownianCubeGlobalExtension f).continuous.comp (by fun_prop))

/-- Apply the order-one RL semigroup iterate to each coordinate-line profile
and evaluate it at the anchor coordinate. -/
def coordinateSemigroupPath {d : ℕ} (i : Fin d) :
    ℕ → C(BrownianCubeAnchor d, ℝ) → C(BrownianCubeAnchor d, ℝ)
  | 0, f => f
  | n + 1, f => by
      let F := coordinateLineProfileFamily i f
      let G : C(BrownianCubeAnchor d, C(UnitInterval, ℝ)) :=
        ⟨fun x => oneIntegralIterate (n + 1) (F x),
          (oneIntegralIterate (n + 1)).continuous.comp F.continuous⟩
      let t : C(BrownianCubeAnchor d, UnitInterval) :=
        ⟨fun x => ⟨x.val i, x.property i⟩,
          ((continuous_apply i).comp continuous_subtype_val).subtype_mk _⟩
      exact ⟨fun x => G x (t x),
        (continuous_eval.comp (G.continuous.prodMk t.continuous))⟩

/-- The actual common-order semigroup path, formed by applying each coordinate
semigroup iterate in the canonical coordinate order. -/
def integrateSheetSemigroupPath {d : ℕ} (m : Fin d → ℕ)
    (f : C(BrownianCubeAnchor d, ℝ)) : C(BrownianCubeAnchor d, ℝ) :=
  (Finset.univ.toList : List (Fin d)).foldl
    (fun g i => coordinateSemigroupPath i (m i) g) f

/-- Repeating ordinary anchored integration `n+1` times in one cube
coordinate is exactly scalar RL integration of integer order `n+1` on that
coordinate line.  The integer-order RL operator is itself the semigroup
iterate of order-one RL. -/
theorem iterateCoordinatePath_eq_orderOne_semigroup {d : ℕ}
    (i : Fin d) (f : C(BrownianCubeAnchor d, ℝ)) (n : ℕ)
    (x : BrownianCubeAnchor d) :
    BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f x =
      oneIntegralIterate (n + 1) (coordinateLineProfile i f x)
        ⟨x.val i, (x.property i)⟩ := by
  have horder : (fractionalOnC ((n + 1 : ℕ) : ℝ) (by
      have : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith)) = oneIntegralIterate (n + 1) :=
    integerOrder_eq_iterate (n + 1) (by omega)
  have hrl : fractionalOnC ((n + 1 : ℕ) : ℝ) (by
      have : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith) (coordinateLineProfile i f x) ⟨x.val i, x.property i⟩ =
      ∫ u in Set.Ioc (0 : ℝ) (x.val i),
        (((n.factorial : ℝ)⁻¹ * (x.val i - u) ^ n) *
          brownianCubeGlobalExtension f (Function.update x.val i u)) ∂volume := by
    rw [fractionalOnC, ContinuousLinearMap.comp_apply]
    have hvol := fractionalRL_natSucc_eq_volterra (n := n)
      (profileToL2 (coordinateLineProfile i f x)) (x.val i)
      (x.property i).1 (x.property i).2
    have hvol' : fractionalRL ((n + 1 : ℕ) : ℝ) (by
        have : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith) (profileToL2 (coordinateLineProfile i f x))
          ⟨x.val i, x.property i⟩ =
        ∫ u in Set.Ioc (0 : ℝ) (x.val i),
          ((n.factorial : ℝ)⁻¹ * (x.val i-u)^n) *
            profileToL2 (coordinateLineProfile i f x) u ∂volume := by
      simpa only [Nat.cast_add, Nat.cast_one] using hvol
    rw [hvol']
    have hsubset : Set.Ioc (0 : ℝ) (x.val i) ⊆ UnitInterval := by
      intro u hu
      exact ⟨hu.1.le, le_trans hu.2 (x.property i).2⟩
    have hmeasure : volume.restrict (Set.Ioc (0 : ℝ) (x.val i)) ≤
        volume.restrict UnitInterval :=
      volume.restrict_mono_set hsubset
    have hprofile : profileToL2 (coordinateLineProfile i f x) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) (x.val i))]
        fun u => coordinateLineProfile i f x (clipUnit u) :=
      ae_mono hmeasure (profileToL2_coe (coordinateLineProfile i f x))
    apply integral_congr_ae
    filter_upwards [hprofile, ae_restrict_mem measurableSet_Ioc] with u hprofile hu
    have hu1 : u ≤ 1 := le_trans hu.2 (x.property i).2
    have hclip : (clipUnit u).val = u := by
      simp [clipUnit, hu.1.le, hu1]
    have hline : coordinateLineProfile i f x (clipUnit u) =
        brownianCubeGlobalExtension f (Function.update x.val i u) := by
      simp [coordinateLineProfile, hclip]
    rw [hprofile, hline]
  calc
    BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f x =
        ∫ u in Set.Ioc (0 : ℝ) (x.val i),
          (((n.factorial : ℝ)⁻¹ * (x.val i - u) ^ n) *
            brownianCubeGlobalExtension f (Function.update x.val i u)) ∂volume :=
      BrownianSharp.AlignmentGaussianBochner.iterateCoordinatePath_eq_normalizedPower
        i f n x
    _ = fractionalOnC ((n + 1 : ℕ) : ℝ) (by
        have : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith) (coordinateLineProfile i f x) ⟨x.val i, x.property i⟩ := hrl.symm
    _ = oneIntegralIterate (n + 1) (coordinateLineProfile i f x)
        ⟨x.val i, x.property i⟩ := by
      exact congrFun (congrArg (fun T => T (coordinateLineProfile i f x)) horder)
        ⟨x.val i, x.property i⟩

/-- Each path-space coordinate integration block is exactly the continuous
path obtained by applying the scalar order-one RL semigroup along its lines. -/
theorem coordinateSemigroupPath_eq_iterateCoordinatePath {d : ℕ}
    (i : Fin d) (n : ℕ) (f : C(BrownianCubeAnchor d, ℝ)) :
    coordinateSemigroupPath i n f = iterateCoordinatePath i n f := by
  cases n with
  | zero => rfl
  | succ n =>
      ext x
      simpa [coordinateSemigroupPath, coordinateLineProfileFamily] using
        (iterateCoordinatePath_eq_orderOne_semigroup i f n x).symm

/-- The full integrated sheet path is the fold of the actual coordinatewise
order-one RL semigroup iterates. This equality is what lets the integrated
small-ball shift route be stated through the semigroup representation. -/
theorem integrateSheetPath_eq_integrateSheetSemigroupPath {d : ℕ}
    (m : Fin d → ℕ) (f : C(BrownianCubeAnchor d, ℝ)) :
    integrateSheetPath m f = integrateSheetSemigroupPath m f := by
  classical
  have hfold : ∀ (l : List (Fin d)) (f : C(BrownianCubeAnchor d, ℝ)),
      l.foldl (fun g i => coordinateSemigroupPath i (m i) g) f =
        l.foldl (fun g i => iterateCoordinatePath i (m i) g) f := by
    intro l
    induction l with
    | nil =>
        intro f
        rfl
    | cons i l ih =>
        intro f
        simp only [List.foldl_cons]
        rw [coordinateSemigroupPath_eq_iterateCoordinatePath]
        exact ih _
  simpa [integrateSheetPath, integrateSheetSemigroupPath] using
    (hfold (Finset.univ.toList) f).symm

end BrownianSharp.AlignmentPaperIntegratedSemigroup
