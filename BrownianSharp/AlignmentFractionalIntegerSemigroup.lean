import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentFractionalL2OperatorSemigroup
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalApproximationNumbers
import Mathlib.Tactic

/-! Actual L² semigroup identities at positive even integer orders. The maps
are the checked Riemann--Liouville operators followed by the actual canonical
continuous-profile embeddings into L². -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalIntegerSemigroup

open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalL2OperatorSemigroup
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalL2

/-- The actual scalar RL operator on unit-interval L². -/
abbrev scalarRLOnL2 (α : ℝ) (hα : 1/2 < α) :
    UnitL2 →L[ℝ] UnitL2 := fractionalRLOnL2 α hα

/-- Actual order-two scalar RL on L². -/
abbrev scalarR2L2 : UnitL2 →L[ℝ] UnitL2 :=
  scalarRLOnL2 2 (by norm_num)

/-- The actual isotropic tensor RL operator on cube L². -/
abbrev tensorRLOnL2 {d : ℕ} (α : ℝ) (hα : 1/2 < α) :
    CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d :=
  fractionalTensorRLToL2 (d:=d) (fun _ => α) (fun _ => hα)

/-- Actual order-two tensor RL on cube L². -/
abbrev tensorR2L2 {d : ℕ} :
    CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d :=
  tensorRLOnL2 (d:=d) 2 (by norm_num)

private theorem scalarRLOnL2_congr {a b : ℝ} (hab : a = b)
    (ha : 1/2 < a) (hb : 1/2 < b) : scalarRLOnL2 a ha = scalarRLOnL2 b hb := by
  subst b
  rfl

private theorem tensorRLOnL2_congr {d : ℕ} {a b : ℝ} (hab : a = b)
    (ha : 1/2 < a) (hb : 1/2 < b) : tensorRLOnL2 (d:=d) a ha = tensorRLOnL2 b hb := by
  subst b
  rfl

/-- Scalar L² RL maps form a semigroup. -/
theorem scalarRLOnL2_semigroup {a b : ℝ} (ha : 1/2 < a) (hb : 1/2 < b) :
    (scalarRLOnL2 a ha).comp (scalarRLOnL2 b hb) =
      scalarRLOnL2 (a+b) (by linarith) := by
  exact fractionalRLOnL2_semigroup ha hb

/-- Scalar order `2m` is the `m`-fold composition of the actual order-two
scalar L² RL operator, for every positive natural `m`. -/
theorem scalarRLOnL2_even_order (m : ℕ) :
    scalarRLOnL2 (2 * ((m+1:ℕ):ℝ)) (by
      have hp : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
      nlinarith) = scalarR2L2 ^ (m+1) := by
  induction m with
  | zero =>
      simp [scalarRLOnL2, scalarR2L2]
  | succ m ih =>
      have ha : (1/2:ℝ) < 2 * ((m+1:ℕ):ℝ) := by
        have hp : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
        nlinarith
      have hs := scalarRLOnL2_semigroup ha (by norm_num : (1/2:ℝ) < 2)
      have harg : 2 * ((m+2:ℕ):ℝ) = 2 * ((m+1:ℕ):ℝ) + 2 := by
        push_cast
        ring
      calc
        scalarRLOnL2 (2 * ((m+2:ℕ):ℝ)) (by
            have hnat : 1 ≤ m+2 := by omega
            have hp : (1:ℝ) ≤ ((m+2:ℕ):ℝ) := by exact_mod_cast hnat
            nlinarith) =
          scalarRLOnL2 (2 * ((m+1:ℕ):ℝ) + 2) (by linarith [ha]) :=
            scalarRLOnL2_congr harg _ _
        _ = (scalarRLOnL2 (2 * ((m+1:ℕ):ℝ)) ha).comp scalarR2L2 := by
          exact hs.symm
        _ = (scalarR2L2 ^ (m+1)).comp scalarR2L2 := by rw [ih]
        _ = scalarR2L2 ^ (m+2) := by simp [pow_succ, ContinuousLinearMap.mul_def]

/-- Tensor L² RL maps form a semigroup, including the intermediate
continuous-profile embedding. -/
theorem tensorRLOnL2_semigroup {d : ℕ} {a b : ℝ}
    (ha : 1/2 < a) (hb : 1/2 < b) :
    (tensorRLOnL2 (d:=d) a ha).comp (tensorRLOnL2 (d:=d) b hb) =
      tensorRLOnL2 (d:=d) (a+b) (by linarith) := by
  apply ContinuousLinearMap.ext
  intro f
  change cubeProfileToL2 (fractionalTensorRL (fun _ : Fin d => a) (fun _ => ha)
      (cubeProfileToL2 (fractionalTensorRL (fun _ : Fin d => b) (fun _ => hb) f))) =
    cubeProfileToL2 (fractionalTensorRL (fun _ : Fin d => a+b)
      (fun _ => by linarith) f)
  have hsem := fractionalTensorRL_semigroup (d:=d) ha hb
  have hsemf := congrArg (fun T => T f) hsem
  simpa [fractionalTensorRLToL2, ContinuousLinearMap.comp_apply] using
    congrArg cubeProfileToL2 hsemf.symm

/-- The isotropic tensor L² RL operator of order `2m` is the `m`-fold
composition of the actual order-two tensor L² operator. This is an equality
on the whole tensor L² source. -/
theorem tensorRLOnL2_even_order {d : ℕ} (m : ℕ) :
    tensorRLOnL2 (d:=d) (2 * ((m+1:ℕ):ℝ)) (by
      have hp : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
      nlinarith) = tensorR2L2 (d:=d) ^ (m+1) := by
  induction m with
  | zero =>
      simp [tensorRLOnL2, tensorR2L2]
  | succ m ih =>
      have ha : (1/2:ℝ) < 2 * ((m+1:ℕ):ℝ) := by
        have hp : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
        nlinarith
      have hs := tensorRLOnL2_semigroup (d:=d) ha (by norm_num : (1/2:ℝ) < 2)
      have harg : 2 * ((m+2:ℕ):ℝ) = 2 * ((m+1:ℕ):ℝ) + 2 := by
        push_cast
        ring
      calc
        tensorRLOnL2 (d:=d) (2 * ((m+2:ℕ):ℝ)) (by
            have hnat : 1 ≤ m+2 := by omega
            have hp : (1:ℝ) ≤ ((m+2:ℕ):ℝ) := by exact_mod_cast hnat
            nlinarith) =
          tensorRLOnL2 (d:=d) (2 * ((m+1:ℕ):ℝ) + 2) (by linarith [ha]) :=
            tensorRLOnL2_congr harg _ _
        _ = (tensorRLOnL2 (d:=d) (2 * ((m+1:ℕ):ℝ)) ha).comp tensorR2L2 := hs.symm
        _ = (tensorR2L2 (d:=d) ^ (m+1)).comp tensorR2L2 := by rw [ih]
        _ = tensorR2L2 (d:=d) ^ (m+2) := by simp [pow_succ, ContinuousLinearMap.mul_def]

/-- Positive-order indexing form of the scalar identity. -/
theorem scalarRLOnL2_even_order_nat {m : ℕ} (hm : 1 ≤ m) :
    scalarRLOnL2 (2 * (m:ℝ)) (by
      have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith) = scalarR2L2 ^ m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  simpa using scalarRLOnL2_even_order n

/-- Positive-order indexing form of the isotropic tensor identity. -/
theorem tensorRLOnL2_even_order_nat {d m : ℕ} (hm : 1 ≤ m) :
    tensorRLOnL2 (d:=d) (2 * (m:ℝ)) (by
      have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith) = tensorR2L2 (d:=d) ^ m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  simpa using tensorRLOnL2_even_order (d:=d) n


end BrownianSharp.AlignmentFractionalIntegerSemigroup
