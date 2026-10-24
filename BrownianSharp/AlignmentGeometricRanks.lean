import BrownianSharp.DKLLRankAllocation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Smoothness-dependent rank allocation. The original certificate fixes a
single geometric ratio; fractional and arbitrary-r periodic rates need an
arbitrary summable profile. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentGeometricRanks

def rank (q : ℝ) (D j : ℕ) : ℕ := ⌊(D:ℝ)*q^j⌋₊

theorem rank_le_profile {q : ℝ} (hq : 0≤q) (D j : ℕ) :
    (rank q D j:ℝ) ≤ (D:ℝ)*q^j := by
  apply Nat.floor_le
  positivity

theorem half_profile_le_rank_add_one {q : ℝ} (hq : 0≤q) (D j : ℕ) :
    (D:ℝ)*q^j/2 ≤ (rank q D j:ℝ)+1 := by
  have hfloor := Nat.self_sub_floor_lt_one (a:=(D:ℝ)*q^j)
  have hnonneg : 0≤(D:ℝ)*q^j := by positivity
  have hrank : 0≤(rank q D j:ℝ) := by positivity
  change (D:ℝ)*q^j - (rank q D j:ℝ) < 1 at hfloor
  linarith

theorem summable_polynomial_geometric {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (k : ℕ) :
    Summable (fun j : ℕ => ((j+1:ℕ):ℝ)^k*q^j) := by
  have hq : ‖q‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hq0]; exact hq1
  have hb := summable_pow_mul_geometric_of_norm_lt_one k hq
  have hs : Summable (fun j : ℕ => ((j+1:ℕ):ℝ)^k*q^(j+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hb
  convert hs.mul_left q⁻¹ using 1
  funext j
  rw [pow_succ]
  field_simp
  <;> ring

def polynomialBudget (q : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, ((j+1:ℕ):ℝ)^k*q^j

theorem polynomialBudget_nonneg {q : ℝ} (hq : 0≤q) (k : ℕ) :
    0≤polynomialBudget q k := by
  apply tsum_nonneg
  intro j
  positivity

theorem sum_rank_le {q : ℝ} (hq0 : 0<q) (hq1 : q<1) (D J : ℕ) :
    ((∑ j ∈ Finset.range J, rank q D j:ℕ):ℝ) ≤ (D:ℝ)/(1-q) := by
  have hq : ‖q‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hq0]; exact hq1
  have hgeom := (summable_geometric_of_norm_lt_one hq).sum_le_tsum
    (s:=Finset.range J) (fun j hj => by positivity)
  have hsum : ∑ j ∈ Finset.range J, q^j ≤ (1-q)⁻¹ := by
    simpa [tsum_geometric_of_norm_lt_one hq] using hgeom
  calc
    ((∑ j ∈ Finset.range J, rank q D j:ℕ):ℝ) =
        ∑ j ∈ Finset.range J, (rank q D j:ℝ) := by push_cast; rfl
    _ ≤ ∑ j ∈ Finset.range J, (D:ℝ)*q^j :=
      Finset.sum_le_sum fun j hj => rank_le_profile hq0.le D j
    _ = (D:ℝ)*(∑ j ∈ Finset.range J, q^j) := by rw [Finset.mul_sum]
    _ ≤ (D:ℝ)*(1-q)⁻¹ := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (D:ℝ)/(1-q) := by rw [div_eq_mul_inv]

theorem finite_error_budget {q ρ A : ℝ} (hρ : 0<ρ) (hρq : ρ<q)
    (hq1 : q<1) (hA : 0≤A) {D : ℕ} (hD : 0<D)
    (k J : ℕ) (e : ℕ→ℝ)
    (he : ∀ j∈Finset.range J, e j^2 ≤
      A*((j+1:ℕ):ℝ)^k*ρ^j/((rank q D j:ℝ)+1)) :
    (∑ j∈Finset.range J,e j^2) ≤
      (2*A/(D:ℝ))*polynomialBudget (ρ/q) k := by
  have hq0 : 0<q := hρ.trans hρq
  have hratio0 : 0<ρ/q := div_pos hρ hq0
  have hratio1 : ρ/q<1 := (div_lt_one hq0).2 hρq
  have hs := summable_polynomial_geometric hratio0 hratio1 k
  have hpoint : ∀ j∈Finset.range J, e j^2 ≤
      (2*A/(D:ℝ))*(((j+1:ℕ):ℝ)^k*(ρ/q)^j) := by
    intro j hj
    have hden := half_profile_le_rank_add_one hq0.le D j
    have hp : 0<(D:ℝ)*q^j := by positivity
    have hfirst := he j hj
    have hd : 0<(rank q D j:ℝ)+1 := by positivity
    have hn : 0≤A*((j+1:ℕ):ℝ)^k*ρ^j := by positivity
    calc
      e j^2 ≤ A*((j+1:ℕ):ℝ)^k*ρ^j/((rank q D j:ℝ)+1) := hfirst
      _ ≤ A*((j+1:ℕ):ℝ)^k*ρ^j/((D:ℝ)*q^j/2) :=
        div_le_div_of_nonneg_left hn (by positivity) hden
      _ = (2*A/(D:ℝ))*(((j+1:ℕ):ℝ)^k*(ρ/q)^j) := by
        rw [div_pow]
        field_simp
        <;> ring
  calc
    (∑ j∈Finset.range J,e j^2) ≤
        ∑ j∈Finset.range J,(2*A/(D:ℝ))*(((j+1:ℕ):ℝ)^k*(ρ/q)^j) :=
      Finset.sum_le_sum hpoint
    _ = (2*A/(D:ℝ))*(∑ j∈Finset.range J,((j+1:ℕ):ℝ)^k*(ρ/q)^j) := by rw [Finset.mul_sum]
    _ ≤ (2*A/(D:ℝ))*polynomialBudget (ρ/q) k :=
      mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum (s:=Finset.range J) (fun j hj => by positivity))
        (by positivity)

end BrownianSharp.AlignmentGeometricRanks
