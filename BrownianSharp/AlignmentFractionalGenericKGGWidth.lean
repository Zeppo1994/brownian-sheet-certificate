import BrownianSharp.AlignmentFractionalKGGArithmetic
import BrownianSharp.AlignmentFractionalSharpBudgets
import BrownianSharp.AlignmentEndpointWidthExtraction
import BrownianSharp.LayerIndex
import BrownianSharp.CubeGridLogBudget
import BrownianSharp.CubeDyadicGrid
import BrownianSharp.CameronMartin
import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! Generic parameter selection for the sharp dyadic KGG profile. -/

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open Topology
set_option maxHeartbeats 1200000

namespace BrownianSharp.AlignmentFractionalGenericKGGWidth

open BrownianSharp.AlignmentFractionalKGGArithmetic
open BrownianSharp.AlignmentFractionalSharpBudgets
open BrownianSharp
open HaarQuarter
open HaarQuarter.TheoremD.Width
open BrownianSharp.AlignmentGeometricRanks
open Filter

/-- If a graded KGG construction has the usual low-rank/geometric-energy
error profile, choose the mesh and rectangular truncation depths and obtain
the sharp dyadic width rate. The profile hypothesis is deliberately separated
from the feature-frame details, so Haar and polynomial frames share this
numeric closure. -/
theorem dyadic_width_of_KGG_profile
    {d ν : ℕ} (hd : 2 ≤ d) (hν : 2 ≤ ν)
    {K : Set C(BrownianCubeAnchor d, ℝ)}
    {Cproj bproj Cmesh β r ρ qrate δ Llog Cenergy : ℝ} {Cdim k : ℕ}
    (hCproj : 0 < Cproj) (hbproj : 0 < bproj) (hbproj1 : bproj < 1)
    (hCmesh : 0 ≤ Cmesh) (hCenergy : 0 ≤ Cenergy)
    (hβ : 0 < β) (hr : 0 < r)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hq : 0 < qrate) (hq1 : qrate < 1)
    (hρq : ρ < qrate) (hρeq : ρ = (2:ℝ)^(-(2*r-1)))
    (hk : k = ν-1) (hCdim : 0 < Cdim) (hδ : 0 < δ)
    (hLlog : 0 ≤ Llog)
    (rankLower : ∀ n : ℕ,
      δ*(2:ℝ)^n*((n+1:ℕ):ℝ)^k ≤
        (Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ))
    (logGrid : ∀ H : ℕ,
      Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) ≤
        Llog*((H+1:ℕ):ℝ))
    (meshBudget : ∃ Km : ℕ, 0 < Km ∧ ∀ n : ℕ,
      (2*((2:ℝ)^(Km*(n+1)))⁻¹)^β ≤ (2:ℝ)^(-r*n))
    (profile : ∀ n M H τ,
      1 ≤ M →
      0 ≤ τ → Cproj*bproj^M ≤ τ →
      kolmogorovWidth K (Cdim*(Nat.ceil (1+(1-qrate)⁻¹)) *
          Fintype.card (LayerIndex ν n)) ≤
        ENNReal.ofReal (τ + Cmesh*(2*((2:ℝ)^H)⁻¹)^β +
          Real.sqrt ((4*(10000:ℝ)^2*((n+2:ℕ):ℝ)^k*ρ^(n+1)*
            Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) /
            ((Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ)))*
            (Cenergy*polynomialBudget (ρ/qrate) k)))) :
    ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      kolmogorovWidth K (A*Fintype.card (LayerIndex ν n)) ≤
        ENNReal.ofReal (B*(2:ℝ)^(-r*n)*Real.sqrt (n+1:ℝ)) := by
  classical
  rcases meshBudget with ⟨Km,hKm,hmesh⟩
  let G : ℕ := Nat.ceil (1+(1-qrate)⁻¹)
  let A : ℕ := Cdim*G
  have hG : 0 < G := by
    dsimp [G]
    apply Nat.ceil_pos.mpr
    have : 0 < 1+(1-qrate)⁻¹ := by positivity
    exact this
  have hA : 0 < A := Nat.mul_pos hCdim hG
  let V : ℝ := (4*(10000:ℝ)^2)*(2:ℝ)^k*ρ*Llog*
    ((Km+1:ℕ):ℝ)*Cenergy*polynomialBudget (ρ/qrate) k / δ
  have hratio0 : 0 < ρ/qrate := div_pos hρ hq
  have hratio1 : ρ/qrate < 1 := (div_lt_one hq).2 hρq
  have hbudget : 0 ≤ polynomialBudget (ρ/qrate) k :=
    polynomialBudget_nonneg hratio0.le k
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  let B : ℝ := 1+Cmesh+Real.sqrt V
  have hB : 0 < B := by
    dsimp [B]
    have := Real.sqrt_nonneg V
    linarith
  refine ⟨A,hA,B,hB,?_⟩
  intro n
  let target : ℝ := (2:ℝ)^(-r*n)*Real.sqrt (n+1:ℝ)
  have htarget : 0 < target := by dsimp [target]; positivity
  let D : ℕ := Cdim*Fintype.card (LayerIndex ν n)
  have hD : 0 < D := by
    dsimp [D]
    have hcard : 0 < Fintype.card (LayerIndex ν n) := by
      rw [layerIndex_card ν n (by omega : 0<ν)]
      apply Nat.mul_pos
      · positivity
      · exact Nat.choose_pos (by omega : ν-1 ≤ n+ν-1)
    exact Nat.mul_pos hCdim hcard
  let H : ℕ := Km*(n+1)
  have hlog : Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) ≤
      (Llog*((Km+1:ℕ):ℝ))*((n+1:ℕ):ℝ) := by
    calc
      _ ≤ Llog*((H+1:ℕ):ℝ) := logGrid H
      _ ≤ Llog*((Km+1:ℕ):ℝ)*((n+1:ℕ):ℝ) := by
        have hnat : (H+1:ℕ) ≤ (Km+1)*(n+1) := by
          dsimp [H]
          calc
            Km*(n+1)+1 ≤ Km*(n+1)+(n+1) := Nat.add_le_add_left (by omega) _
            _ = (Km+1)*(n+1) := by ring
        have hc : ((H+1:ℕ):ℝ) ≤ (((Km+1)*(n+1):ℕ):ℝ) := by exact_mod_cast hnat
        rw [Nat.cast_mul, Nat.cast_add] at hc
        have := mul_le_mul_of_nonneg_left hc hLlog
        rw [Nat.cast_add]
        simpa [Nat.cast_mul, mul_assoc] using this
  have hseq : ∀ᶠ M : ℕ in atTop, Cproj*bproj^M < target := by
    have hp : Tendsto (fun M : ℕ => bproj^M) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hbproj.le hbproj1
    have hm : Tendsto (fun M : ℕ => Cproj*bproj^M) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hp
    exact hm.eventually (Iio_mem_nhds htarget)
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.1 hseq
  let M : ℕ := max M₀ (n+1)
  have hMcut : 1 ≤ M := by
    dsimp [M]
    omega
  have hsmall : Cproj*bproj^M ≤ target := by
    apply (hM₀ M (le_max_left _ _)).le
  have hMpos : 1 ≤ M := hMcut
  have hprofile := profile n M H target hMpos (le_of_lt htarget) hsmall
  have hmesh' : Cmesh*(2*((2:ℝ)^H)⁻¹)^β ≤ Cmesh*(2:ℝ)^(-r*n) :=
    mul_le_mul_of_nonneg_left (by simpa [H] using hmesh n) hCmesh
  have hJ : Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) ≤
      (Llog*((Km+1:ℕ):ℝ))*((n+1:ℕ):ℝ) := hlog
  have hnorm : δ*(2:ℝ)^n*((n+1:ℕ):ℝ)^k ≤
      (Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ) := rankLower n
  have hJ0 : 0 ≤ Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) := by
    apply Real.log_nonneg
    have hc : 0 ≤ (Fintype.card (CubeDyadicGrid d H):ℝ) := Nat.cast_nonneg _
    nlinarith
  have hKGG := sharp_KGG_sqrt_bound
    (C:=4*(10000:ℝ)^2) (B:=Cenergy*polynomialBudget (ρ/qrate) k)
    (L:=Llog*((Km+1:ℕ):ℝ)) (δ:=δ)
    (D:=(Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ))
    (J:=Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2))
    (r:=r) (by positivity)
    (mul_nonneg hCenergy (polynomialBudget_nonneg (by positivity) k))
    (mul_nonneg hLlog (by positivity)) hδ
    hJ0 k n hnorm hJ
  have hKGG' : Real.sqrt ((4*(10000:ℝ)^2*((n+2:ℕ):ℝ)^k*ρ^(n+1)*
      Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2)/
        ((Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ)))*
      (Cenergy*polynomialBudget (ρ/qrate) k)) ≤ Real.sqrt V*target := by
    rw [← hρeq] at hKGG
    dsimp [V,target]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hKGG
  have herr : target+Cmesh*(2:ℝ)^(-r*n)+Real.sqrt V*target ≤ B*target := by
    dsimp [B]
    have ht : (2:ℝ)^(-r*n) ≤ target := by
      dsimp [target]
      have hs : 1 ≤ Real.sqrt (n+1:ℝ) := by
        have hn : (1:ℝ) ≤ (n+1:ℕ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
        simpa using Real.sqrt_le_sqrt hn
      nlinarith [mul_le_mul_of_nonneg_left hs (show 0≤(2:ℝ)^(-r*n) by positivity)]
    have := mul_le_mul_of_nonneg_left ht hCmesh
    nlinarith
  have hfinal : kolmogorovWidth K (Cdim*G*Fintype.card (LayerIndex ν n)) ≤
      ENNReal.ofReal (B*target) := by
    apply le_trans hprofile
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ target+Cmesh*(2:ℝ)^(-r*n)+Real.sqrt V*target := by
        exact add_le_add (add_le_add le_rfl hmesh') hKGG'
      _ ≤ B*target := herr
  have hAeq : Cdim*G*Fintype.card (LayerIndex ν n) =
      A*Fintype.card (LayerIndex ν n) := by rfl
  rw [hAeq] at hfinal
  convert hfinal using 1 <;> congr 1 <;> ring

end BrownianSharp.AlignmentFractionalGenericKGGWidth
