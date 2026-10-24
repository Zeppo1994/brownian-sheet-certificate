import BrownianSharp.DKLLFiniteLayerRate
import BrownianSharp.ShapeGrowth
import BrownianSharp.LayerIndex

/-! Concrete scalar estimate for one high-grade block. This is the key
normalization step: grid logarithm divided by allocated rank cancels the base
hyperbolic dimension, leaving a polynomial in the grade offset and a summable
geometric factor. -/

namespace BrownianSharp.DKLLLayerError

open BrownianSharp.DKLLRankAllocation
open BrownianSharp.DKLLFiniteLayerRate

noncomputable section

set_option maxHeartbeats 600000

private theorem inverse_dyadic_pow_div_layerRatio (j : ℕ) :
    ((2 : ℝ) ^ j)⁻¹ / layerRatio ^ j = layerRatio ^ j := by
  have hsquare : layerRatio ^ 2 = (1 / 2 : ℝ) := by
    rw [layerRatio, Real.sq_sqrt]
    norm_num
  have hpow : ((2 : ℝ) ^ j)⁻¹ = layerRatio ^ j * layerRatio ^ j := by
    calc
      ((2 : ℝ) ^ j)⁻¹ = (1 / 2 : ℝ) ^ j := by
        rw [one_div_pow]
        norm_num
      _ = (layerRatio ^ 2) ^ j := by rw [← hsquare]
      _ = layerRatio ^ j * layerRatio ^ j := by
        rw [← pow_mul]
        have hidx : 2 * j = j + j := by omega
        rw [hidx, pow_add]
  rw [hpow]
  have hrj : layerRatio ^ j ≠ 0 := ne_of_gt (pow_pos layerRatio_pos j)
  field_simp

private theorem layer_factor_identity (n j : ℕ) (S Snext G : ℝ)
    (hS : 0 < S) :
    ((2 : ℝ) ^ (n + j))⁻¹ * Snext *
        (G * ((n : ℝ) + 1) /
          ((2 : ℝ) ^ n * S * layerRatio ^ j / 8)) =
      8 * G * ((n : ℝ) + 1) * dyadicSquare n *
        (Snext / S) * layerRatio ^ j := by
  rw [pow_add]
  have h2n : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (by positivity)
  have hrj : layerRatio ^ j ≠ 0 := ne_of_gt (pow_pos layerRatio_pos j)
  have hsn : S ≠ 0 := ne_of_gt hS
  have hprod : (2 : ℝ) ^ j * (layerRatio ^ j * layerRatio ^ j) = 1 := by
    have hpow := inverse_dyadic_pow_div_layerRatio j
    field_simp at hpow ⊢
    nlinarith [hpow]
  unfold dyadicSquare
  field_simp
  calc
    Snext * G = Snext * G * ((2 : ℝ) ^ j * (layerRatio ^ j * layerRatio ^ j)) := by
      rw [hprod]
      ring_nf
    _ = (2 : ℝ) ^ j * Snext * G * (layerRatio ^ j) ^ 2 := by ring_nf

private theorem hyperbolic_offset_ratio_le {d n j : ℕ} (hd : 1 ≤ d) :
    hyperbolicCount d (n + j) / hyperbolicCount d n ≤
      (Nat.factorial (d - 1) : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (d - 1)) := by
  have hr := hyperbolicCount_ratio_le hd n (n + j)
  have harg : ((((n + j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) ≤
      ((j + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    push_cast
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    nlinarith [mul_nonneg hn0 hj0]
  exact hr.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) harg (d - 1)) (by positivity))

/-- One KGG block error, with the actual half-base-rank geometric allocation.
The hypotheses are the raw row-radius estimate, the grid-log bound, and the
standard hyperbolic-count ratio bound. In applications `S` and `Snext` are
`hyperbolicCount d n` and `hyperbolicCount d (n+j)`. -/
theorem allocated_layer_error_squared_le
    {d n j D : ℕ} (hd : 1 ≤ d) (S Snext M G K radiusSq error : ℝ)
    (hD : (D : ℝ) = (2 : ℝ) ^ n * S)
    (hDlarge : 4 ≤ D)
    (hS : 0 < S)
    (hSnext : 0 ≤ Snext)
    (hRadiusNonneg : 0 ≤ radiusSq)
    (hSratio : Snext / S ≤
      (Nat.factorial (d - 1) : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (d - 1)))
    (hM : 0 ≤ M) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hgrid : M ≤ G * ((n : ℝ) + 1))
    (hradius : radiusSq ≤ ((2 : ℝ) ^ (n + j))⁻¹ * Snext)
    (herror : error ^ 2 ≤ K ^ 2 * radiusSq *
      (M / ((allocatedRank (D / 2) j : ℝ) + 1))) :
    error ^ 2 ≤ 8 * K ^ 2 * G * (Nat.factorial (d - 1) : ℝ) *
      ((n : ℝ) + 1) * dyadicSquare n *
      (((j + 1 : ℕ) : ℝ) ^ (d - 1)) * layerRatio ^ j := by
  have hden := allocated_denominator_lower D j hDlarge
  have hdenpos : 0 < (D : ℝ) * layerRatio ^ j / 8 := by
    have hDr : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    exact div_pos (mul_pos hDr (pow_pos layerRatio_pos j)) (by norm_num)
  have hquot : M / ((allocatedRank (D / 2) j : ℝ) + 1) ≤
      M / ((D : ℝ) * layerRatio ^ j / 8) :=
    div_le_div_of_nonneg_left hM hdenpos hden
  have hquotGrid : M / ((D : ℝ) * layerRatio ^ j / 8) ≤
      G * ((n : ℝ) + 1) / ((D : ℝ) * layerRatio ^ j / 8) :=
    div_le_div_of_nonneg_right hgrid hdenpos.le
  have hfac : 0 ≤ K ^ 2 * radiusSq := mul_nonneg (sq_nonneg K) hRadiusNonneg
  calc
    error ^ 2 ≤ K ^ 2 * radiusSq *
        (M / ((allocatedRank (D / 2) j : ℝ) + 1)) := herror
    _ ≤ K ^ 2 * radiusSq * (M / ((D : ℝ) * layerRatio ^ j / 8)) :=
      mul_le_mul_of_nonneg_left hquot hfac
    _ ≤ K ^ 2 * (((2 : ℝ) ^ (n + j))⁻¹ * Snext) *
        (M / ((D : ℝ) * layerRatio ^ j / 8)) := by
      have hmul := mul_le_mul_of_nonneg_right hradius
        (div_nonneg hM hdenpos.le)
      nlinarith [hmul]
    _ ≤ K ^ 2 * (((2 : ℝ) ^ (n + j))⁻¹ * Snext) *
        (G * ((n : ℝ) + 1) / ((D : ℝ) * layerRatio ^ j / 8)) := by
      apply mul_le_mul_of_nonneg_left hquotGrid
      exact mul_nonneg (sq_nonneg K)
        (mul_nonneg (inv_nonneg.mpr (by positivity)) hSnext)
    _ = K ^ 2 * (8 * G * ((n : ℝ) + 1) * dyadicSquare n *
        (Snext / S) * layerRatio ^ j) := by
          calc
            _ = K ^ 2 * ((((2 : ℝ) ^ (n + j))⁻¹ * Snext) *
                (G * ((n : ℝ) + 1) /
                  ((2 : ℝ) ^ n * S * layerRatio ^ j / 8))) := by
              rw [hD]
              ring
            _ = K ^ 2 * (8 * G * ((n : ℝ) + 1) * dyadicSquare n *
                (Snext / S) * layerRatio ^ j) := by
              apply congrArg (fun x : ℝ => K ^ 2 * x)
              exact layer_factor_identity n j S Snext G hS
    _ = 8 * K ^ 2 * G * ((n : ℝ) + 1) * dyadicSquare n *
        (Snext / S) * layerRatio ^ j := by ring
    _ ≤ 8 * K ^ 2 * G * (Nat.factorial (d - 1) : ℝ) *
        ((n : ℝ) + 1) * dyadicSquare n *
        (((j + 1 : ℕ) : ℝ) ^ (d - 1)) * layerRatio ^ j := by
      have hcoef : 0 ≤ 8 * K ^ 2 * G * ((n : ℝ) + 1) *
          dyadicSquare n * layerRatio ^ j := by
        have hbase : 0 ≤ 8 * K ^ 2 * G * ((n : ℝ) + 1) := by positivity [hG]
        exact mul_nonneg (mul_nonneg hbase (dyadicSquare_nonneg n))
          (pow_nonneg layerRatio_nonneg j)
      calc
        _ = (8 * K ^ 2 * G * ((n : ℝ) + 1) * dyadicSquare n *
            layerRatio ^ j) * (Snext / S) := by ring
        _ ≤ (8 * K ^ 2 * G * ((n : ℝ) + 1) * dyadicSquare n *
            layerRatio ^ j) *
            ((Nat.factorial (d - 1) : ℝ) *
              (((j + 1 : ℕ) : ℝ) ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left hSratio hcoef
        _ = _ := by ring

/-- The actual Haar-grid KGG block profile. The row-radius input is exactly
`sqrt(hyperbolicCount(d,n+j)/2^(n+j))`; the grid logarithm is bounded by
`2(d+2)(n+1)`. The conclusion retains the polynomial/geometric offset that
is then summed by `DKLLRankAllocation.layerBudget`. -/
theorem native_haar_allocated_layer_error_squared_le
    {d n j : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (C Ln : ℝ) (hC : 0 ≤ C) (hLn : 0 ≤ Ln)
    (hLnupper : Ln ≤ 2 * ((d : ℝ) + 2) * ((n : ℝ) + 1)) :
    (C * Real.sqrt
        (hyperbolicCount d (n + j) / (2 : ℝ) ^ (n + j)) *
      Real.sqrt (Ln /
        ((allocatedRank (Fintype.card (LayerIndex d n) / 2) j : ℝ) + 1))) ^ 2 ≤
      16 * C ^ 2 * ((d : ℝ) + 2) * (Nat.factorial (d - 1) : ℝ) *
        ((n : ℝ) + 1) * dyadicSquare n *
        (((j + 1 : ℕ) : ℝ) ^ (d - 1)) * layerRatio ^ j := by
  let D := Fintype.card (LayerIndex d n)
  let S := hyperbolicCount d n
  let Snext := hyperbolicCount d (n + j)
  have hS : 0 < S := hyperbolicCount_pos (n := n) (by omega : 1 ≤ d)
  have hSnext : 0 ≤ Snext :=
    (hyperbolicCount_pos (n := n + j) (by omega : 1 ≤ d)).le
  have hD : (D : ℝ) = (2 : ℝ) ^ n * S := by
    dsimp [D, S]
    rw [layerIndex_card d n (by omega)]
    simp [hyperbolicCount]
  have hDreal : 4 ≤ (D : ℝ) := by
    have hpower : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show 2 ≤ n by omega)
      norm_num at hp ⊢
      exact hp
    have hSge : (1 : ℝ) ≤ S := by
      dsimp [S, hyperbolicCount]
      exact_mod_cast (Nat.succ_le_of_lt
        (Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)))
    rw [hD]
    nlinarith [mul_le_mul_of_nonneg_left hSge (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
  have hDlarge : 4 ≤ D := by exact_mod_cast hDreal
  have hSratio : Snext / S ≤
      (Nat.factorial (d - 1) : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (d - 1)) := by
    exact hyperbolic_offset_ratio_le (by omega)
  have hlog : 0 ≤ Ln := hLn
  have hgrid : Ln ≤ (2 * ((d : ℝ) + 2)) * ((n : ℝ) + 1) := by
    simpa [mul_assoc] using hLnupper
  have hradNonneg : 0 ≤ Snext / (2 : ℝ) ^ (n + j) := by positivity
  have hquotNonneg : 0 ≤ Ln /
      ((allocatedRank (D / 2) j : ℝ) + 1) := by positivity
  have hrad : Snext / (2 : ℝ) ^ (n + j) ≤
      ((2 : ℝ) ^ (n + j))⁻¹ * Snext := by
    have heq : Snext / (2 : ℝ) ^ (n + j) =
        ((2 : ℝ) ^ (n + j))⁻¹ * Snext := by ring
    rw [heq]
  have herr :
      (C * Real.sqrt (Snext / (2 : ℝ) ^ (n + j)) *
        Real.sqrt (Ln / ((allocatedRank (D / 2) j : ℝ) + 1))) ^ 2 ≤
      C ^ 2 * (Snext / (2 : ℝ) ^ (n + j)) *
        (Ln / ((allocatedRank (D / 2) j : ℝ) + 1)) := by
    simp only [mul_pow, Real.sq_sqrt hradNonneg, Real.sq_sqrt hquotNonneg]
    exact le_of_eq rfl
  have hper := allocated_layer_error_squared_le (d := d) (n := n) (j := j)
    (D := D) (by omega) (S := S) (Snext := Snext) (M := Ln)
    (G := 2 * ((d : ℝ) + 2)) (K := C)
    (radiusSq := Snext / (2 : ℝ) ^ (n + j))
    (error := C * Real.sqrt (Snext / (2 : ℝ) ^ (n + j)) *
      Real.sqrt (Ln / ((allocatedRank (D / 2) j : ℝ) + 1)))
    hD hDlarge hS hSnext hradNonneg hSratio hlog
    (by positivity) hC hgrid hrad herr
  have hperEq := hper
  have hcoeff : 8 * C ^ 2 * (2 * ((d : ℝ) + 2)) =
      16 * C ^ 2 * ((d : ℝ) + 2) := by ring
  rw [hcoeff] at hperEq
  simpa only [D, S, Snext, mul_assoc, mul_left_comm, mul_comm] using hperEq


end
end BrownianSharp.DKLLLayerError
