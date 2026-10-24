import BrownianSharp.FiniteDictionaryLayerAssembly
import BrownianSharp.AlignmentGeometricRanks
import BrownianSharp.GaussianDictionaryApproximation
import Mathlib.Tactic

/-! Algebraic assembly for geometrically allocated periodic Hilbert-feature
layers. The analytic layer energy estimates are deliberately inputs so this
module can be reused once a concrete Fourier or Haar feature decomposition is
available. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPeriodicWidthLayerAlgebra

open BrownianSharp.AlignmentGeometricRanks

theorem finite_geometric_hilbert_layer_dictionary_assembly
    {I G : Type} [Fintype I] [Fintype G]
    {C q ρ A₀ : ℝ} (hC : 10000 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hρ : 0 < ρ) (hρq : ρ < q) (hA₀ : 0 ≤ A₀)
    {D L k : ℕ} (hD : 0 < D)
    (σ : I → Option (Fin L)) (v : G → EuclideanSpace ℝ I)
    (R : Fin L → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g, ‖BrownianSharp.coordinateLayerMask σ (some j) (v g)‖ ≤ R j)
    (henergy : ∀ j, (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val))
    (hlow : Fintype.card {i : I // σ i = none} ≤ D) :
    ∃ W : Submodule ℝ (G → ℝ),
      Module.rank ℝ W ≤ ((D*Nat.ceil (1+(1-q)⁻¹):ℕ):Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖ ≤ 1 → ∃ y ∈ W,
        ‖BrownianSharp.finiteRowLinear v x-y‖ ≤
          Real.sqrt ((4*C^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/D) *
            polynomialBudget (ρ/q) k) := by
  classical
  have hfin : BrownianSharp.FinDictionaryApproximation 10000 :=
    BrownianSharp.GaussianRIP.finDictionaryApproximation_gaussian
  let m : Fin L → ℕ := fun j => rank q D j.val
  let err : Fin L → ℝ := fun j => 10000*R j*Real.sqrt
    (Real.log (2*(Fintype.card G:ℝ)+2)/((m j:ℝ)+1))
  let Aerr : ℝ := (10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)
  have hlogpos : 0 < Real.log (2*(Fintype.card G:ℝ)+2) := by
    apply Real.log_pos
    have hcard : (0:ℝ) ≤ (Fintype.card G:ℝ) := Nat.cast_nonneg _
    nlinarith
  have hAerr : 0 ≤ Aerr := by dsimp [Aerr]; positivity
  have herr : ∀ j : Fin L,
      (err j)^2 ≤ Aerr*((j.val+1:ℕ):ℝ)^k*ρ^(j.val)/((m j:ℝ)+1) := by
    intro j
    have hden : 0 < (m j:ℝ)+1 := by positivity
    have hfrac : 0 ≤ Real.log (2*(Fintype.card G:ℝ)+2)/((m j:ℝ)+1) :=
      div_nonneg hlogpos.le hden.le
    have hsquare : (err j)^2 =
        (10000:ℝ)^2*(R j)^2*Real.log (2*(Fintype.card G:ℝ)+2)/((m j:ℝ)+1) := by
      dsimp [err]
      rw [mul_pow, Real.sq_sqrt hfrac]
      ring
    rw [hsquare]
    have henergyj := henergy j
    have hmul := mul_le_mul_of_nonneg_right henergyj
      (show 0 ≤ (10000:ℝ)^2*Real.log (2*(Fintype.card G:ℝ)+2) by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul hden.le
    calc
      (10000:ℝ)^2*(R j)^2*Real.log (2*(Fintype.card G:ℝ)+2)/((m j:ℝ)+1) ≤
          A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val)*
            ((10000:ℝ)^2*Real.log (2*(Fintype.card G:ℝ)+2))/((m j:ℝ)+1) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
      _ = Aerr*((j.val+1:ℕ):ℝ)^k*ρ^(j.val)/((m j:ℝ)+1) := by
        dsimp [Aerr]
        ring
  obtain ⟨W,hWrank,hWapprox⟩ :=
    BrownianSharp.finiteRow_dictionary_layer_assembly hfin (by norm_num)
      σ v m R hR hrow
  let errNat : ℕ → ℝ := fun j => if hj : j < L then err ⟨j,hj⟩ else 0
  have hsumErr := finite_error_budget hρ hρq hq1 hAerr hD k L
    errNat
    (by
      intro j hj
      have hjL : j < L := Finset.mem_range.mp hj
      have h := herr ⟨j, hjL⟩
      simpa [errNat, hjL, err,m,rank] using h)
  have hsumEq : (∑ j : Fin L, (err j)^2) =
      ∑ j ∈ Finset.range L, (errNat j)^2 := by
    calc
      (∑ j : Fin L, (err j)^2) = ∑ j : Fin L, (errNat j.val)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [errNat]
      _ = ∑ j ∈ Finset.range L, (errNat j)^2 :=
        Fin.sum_univ_eq_sum_range (fun j => (errNat j)^2) L
  have hsumBound : (∑ j : Fin L, (err j)^2) ≤
      (2*Aerr/(D:ℝ))*polynomialBudget (ρ/q) k := by
    rw [hsumEq]
    exact hsumErr
  have hsumrank := sum_rank_le hq hq1 D L
  have hdenq : 0 < 1-q := by linarith
  have hceil : 1+(1-q)⁻¹ ≤ (Nat.ceil (1+(1-q)⁻¹):ℝ) := by
    exact_mod_cast (Nat.le_ceil (1+(1-q)⁻¹))
  have hsumreal : (∑ j ∈ Finset.range L, (rank q D j:ℝ)) ≤ D/(1-q) := by
    simpa only [Nat.cast_sum] using hsumrank
  have hlowreal : (Fintype.card {i : I // σ i = none}:ℝ) ≤ D := by exact_mod_cast hlow
  have htotalreal : (Fintype.card {i : I // σ i = none}:ℝ) +
      (∑ j ∈ Finset.range L, (rank q D j:ℝ)) ≤
        (D:ℝ)*(Nat.ceil (1+(1-q)⁻¹):ℝ) := by
    calc
      _ ≤ D + D/(1-q) := add_le_add hlowreal hsumreal
      _ = (D:ℝ)*(1+(1-q)⁻¹) := by ring
      _ ≤ (D:ℝ)*(Nat.ceil (1+(1-q)⁻¹):ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by positivity)
  have htotalNat : Fintype.card {i : I // σ i = none}+
      ∑ j ∈ Finset.range L, rank q D j ≤ D*Nat.ceil (1+(1-q)⁻¹) := by
    have hcast : ((Fintype.card {i : I // σ i = none}+
        ∑ j ∈ Finset.range L, rank q D j:ℕ):ℝ) =
        (Fintype.card {i : I // σ i = none}:ℝ)+
          (∑ j ∈ Finset.range L, (rank q D j:ℝ)) := by push_cast; rfl
    exact_mod_cast (hcast ▸ htotalreal)
  have htotal : Fintype.card {i : I // σ i = none}+∑ j : Fin L, m j ≤
      D*Nat.ceil (1+(1-q)⁻¹) := by
    have hsumcast : (∑ j : Fin L, m j) =
        ∑ j ∈ Finset.range L, rank q D j := by
      simpa [m] using (Fin.sum_univ_eq_sum_range (fun j => rank q D j) L)
    rw [hsumcast]
    exact htotalNat
  refine ⟨W, ?_, ?_⟩
  · exact hWrank.trans (by exact_mod_cast htotal)
  · intro x hx
    obtain ⟨y,hy,hyerr⟩ := hWapprox x hx
    refine ⟨y,hy,?_
      ⟩
    have heq : (∑ j : Fin L,
        ((10000:ℝ)*R j*Real.sqrt
          (Real.log (2*(Fintype.card G:ℝ)+2)/((m j:ℝ)+1)))^2) =
        ∑ j : Fin L, (err j)^2 := by
      simp [err]
    rw [heq] at hyerr
    have hroot := Real.sqrt_le_sqrt hsumBound
    have hconst : (2*Aerr/(D:ℝ))*polynomialBudget (ρ/q) k ≤
        (4*C^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/D)*
          polynomialBudget (ρ/q) k := by
      have hpoly : 0 ≤ polynomialBudget (ρ/q) k :=
        polynomialBudget_nonneg (by positivity) k
      dsimp [Aerr]
      have hcoeff : 2*(10000:ℝ)^2 ≤ 4*C^2 := by nlinarith
      have hcoeff' := mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (mul_nonneg hA₀ hlogpos.le) hpoly)
      have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
      field_simp [ne_of_gt hDpos]
      have hlogarg : 2*((Fintype.card G:ℝ)+1) =
          2+(Fintype.card G:ℝ)*2 := by ring
      rw [hlogarg]
      ring_nf at hcoeff' ⊢
      nlinarith [hcoeff']
    have hroot' : Real.sqrt ((2*Aerr/(D:ℝ))*polynomialBudget (ρ/q) k) ≤
        Real.sqrt ((4*C^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/D)*
          polynomialBudget (ρ/q) k) := Real.sqrt_le_sqrt hconst
    exact hyerr.trans (hroot.trans hroot')

end BrownianSharp.AlignmentPeriodicWidthLayerAlgebra
