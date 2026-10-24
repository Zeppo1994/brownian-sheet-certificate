import BrownianSharp.AlignmentFractionalPastSourceEmbedding
import BrownianSharp.AlignmentFractionalPastTailL2Approx
import BrownianSharp.AlignmentFractionalPastTail
import BrownianSharp.AlignmentFractionalPolynomialSpaces
import BrownianSharp.AlignmentFractionalPolynomialBands
import BrownianSharp.AlignmentExponentialPastTailApprox
import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentFractionalPolynomialFrameNonempty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Scalar full-line filtration interfaces for the two-sided MvN feature.

The positive-time polynomial and reflected-past Taylor pieces are kept as
actual subspaces of the full-line source Hilbert space. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianMvNFullLineFiltration

open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalPastSourceEmbedding
open BrownianSharp.AlignmentFractionalPastTailL2Approx
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalSheetPositive
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalPastTail
open BrownianSharp.AlignmentFractionalSheetRKHS
open BrownianSharp.AlignmentFractionalPolynomialBands
open BrownianSharp.AlignmentExponentialPastTailApprox
open BrownianSharp.AlignmentFractionalPastTailFiltration
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalPolynomialFrameNonempty
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionEnergy
open BrownianSharp.AlignmentNestedProjectionBasis

/-- The reflected past tail as an actual element of the positive half-line
source space. -/
noncomputable def pastTailSourceVector (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : PastPositiveL2 :=
  (pastTailPower_memLp_two (by linarith) (by linarith) ht0 ht1).toLp
    (pastTailPower (H-1/2) t)

/-- The causal part of the MvN feature in the unit-interval source space. -/
noncomputable def positiveMvNSourceVector (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UnitL2 :=
  Real.Gamma (H+1/2) • kernelVector (H+1/2) t (by linarith) ht0 ht1

theorem positiveMvNSourceVector_full_ae (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) :
      ℝ → ℝ) =ᵐ[volume] mvNPositiveKernel (H-1/2) t := by
  let g := positiveMvNSourceVector H t hH0 hH1 ht0 ht1
  have hext : (positiveSourceExtension g : ℝ → ℝ) =ᵐ[volume]
      positiveSourceExtensionFunction g :=
    MemLp.coeFn_toLp (positiveSourceExtension_memLp g)
  have hmul := Lp.coeFn_smul (Real.Gamma (H+1/2))
    (kernelVector (H+1/2) t (by linarith) ht0 ht1)
  have hk := MemLp.coeFn_toLp
    (causalKernel_memLp_unit (by linarith : 1/2 < H+1/2) ht0 ht1)
  have hk' : ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) 1 →
      (kernelVector (H+1/2) t (by linarith) ht0 ht1 : ℝ → ℝ) u =
        causalKernel (H+1/2) t u :=
    (ae_restrict_iff' measurableSet_Icc).1 hk
  have hmul' : ∀ᵐ u ∂volume, u ∈ Set.Icc (0:ℝ) 1 →
      (g : ℝ → ℝ) u = Real.Gamma (H+1/2) *
        (kernelVector (H+1/2) t (by linarith) ht0 ht1 : ℝ → ℝ) u := by
    have hsmul' := (ae_restrict_iff' measurableSet_Icc).1 hmul
    filter_upwards [hsmul'] with u hu hmem
    simpa [g, positiveMvNSourceVector, smul_eq_mul] using hu hmem
  have hpos : positiveSourceExtensionFunction g =ᵐ[volume]
      mvNPositiveKernel (H-1/2) t := by
    filter_upwards [hk', hmul', Measure.ae_ne (volume : Measure ℝ) (0:ℝ),
      Measure.ae_ne (volume : Measure ℝ) (1:ℝ)] with u hu hsmul hzero hone
    by_cases hmem : u ∈ Set.Icc (0:ℝ) 1
    · have hu0 : 0 < u := by
        rcases hmem with ⟨hlo,hhi⟩
        exact lt_of_le_of_ne hlo (Ne.symm hzero)
      have hu1 : u < 1 := lt_of_le_of_ne hmem.2 hone
      have heq := mvNPositiveKernel_eq_indicator (by linarith : -(1/2:ℝ)<H-1/2)
        ht1 u
      have hc : causalKernel (H+1/2) t u = kernelCut (H+1/2) (t-u) := by
        symm
        exact kernelCut_translate_eq_causal (α:=H+1/2) ht0 ht1
          (le_of_lt hu0) hu1.le
      change (Set.Icc (0:ℝ) 1).indicator (fun x => (g : ℝ → ℝ) x) u =
        mvNPositiveKernel (H-1/2) t u
      rw [Set.indicator_of_mem hmem, heq]
      calc
        (g : ℝ → ℝ) u = Real.Gamma (H+1/2) *
            causalKernel (H+1/2) t u := by rw [hsmul hmem, hu hmem]
        _ = (Set.Ioi (0:ℝ)).indicator
            (fun x => Real.Gamma (H-1/2+1) * kernelCut (H-1/2+1) (t-x)) u := by
          rw [hc]
          simp only [show H-1/2+1=H+1/2 by ring]
          simp [Set.indicator, hu0]
    · have hzeroPos : (positiveSourceExtensionFunction g) u = 0 := by
        simp [positiveSourceExtensionFunction, Set.indicator, hmem]
      have hmv : mvNPositiveKernel (H-1/2) t u = 0 := by
        by_cases hu0 : 0 < u
        · have hu1 : 1 < u := by
            by_contra hn
            have : u ≤ 1 := le_of_not_gt hn
            exact hmem ⟨le_of_lt hu0,this⟩
          rw [mvNPositiveKernel_eq_indicator (by linarith : -(1/2:ℝ)<H-1/2) ht1]
          simp only [Set.indicator, Set.mem_Ioi, if_pos hu0]
          have hneg : ¬ 0 < t-u := by linarith
          simp [kernelCut, Set.mem_Ioc, hneg]
        · rw [mvNPositiveKernel_eq_indicator (by linarith : -(1/2:ℝ)<H-1/2) ht1]
          simp [Set.indicator, Set.mem_Ioi, hu0]
      rw [hzeroPos, hmv]
  filter_upwards [hext, hpos] with u hext hu
  exact hext.trans hu

/-- The actual unnormalized full-line MvN feature splits into its positive
causal source and the reflected negative-time Taylor source. -/
theorem mvNFullFeature_eq_positive_add_past (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mvNFullFeature (H-1/2) t
      (mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩) =
    positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) +
      negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1) := by
  apply Lp.ext
  have hmem : MemLp (mvNFullKernel (H-1/2) t) 2 volume :=
    mvNFullKernel_memLp hH0 hH1 (by constructor <;> assumption)
  have hfull := MemLp.coeFn_toLp hmem
  have hpos := positiveMvNSourceVector_full_ae H t hH0 hH1 ht0 ht1
  have htail := negativeSourceEmbedding_ae
    (pastTailSourceVector H t hH0 hH1 ht0 ht1)
  have hsrc : (pastTailSourceVector H t hH0 hH1 ht0 ht1 : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Ioi (0:ℝ))] pastTailPower (H-1/2) t := by
    exact MemLp.coeFn_toLp (pastTailPower_memLp_two (by linarith) (by linarith)
      ht0 ht1)
  have hsrc' : ∀ᵐ x ∂volume, x ∈ Set.Ioi (0:ℝ) →
      (pastTailSourceVector H t hH0 hH1 ht0 ht1 : ℝ → ℝ) x =
        pastTailPower (H-1/2) t x :=
    (ae_restrict_iff' measurableSet_Ioi).1 hsrc
  have hsrcInd : pastPositiveExtensionFunction
      (pastTailSourceVector H t hH0 hH1 ht0 ht1) =ᵐ[volume]
      (Set.Ioi (0:ℝ)).indicator (pastTailPower (H-1/2) t) := by
    filter_upwards [hsrc'] with x hx
    by_cases hx0 : 0 < x
    · change (if x ∈ Set.Ioi (0:ℝ) then
        (pastTailSourceVector H t hH0 hH1 ht0 ht1 : ℝ → ℝ) x else 0) =
        (if x ∈ Set.Ioi (0:ℝ) then pastTailPower (H-1/2) t x else 0)
      simp [hx0, hx hx0]
    · simp [pastPositiveExtensionFunction, Set.indicator, hx0]
  have hsourceFull : (pastPositiveExtension
      (pastTailSourceVector H t hH0 hH1 ht0 ht1) : ℝ → ℝ) =ᵐ[volume]
      (Set.Ioi (0:ℝ)).indicator (pastTailPower (H-1/2) t) := by
    exact (pastPositiveExtension_ae _).trans hsrcInd
  have hsplit := mvNFullKernel_eq_positive_add_past_ae (H:=H) (t:=t)
    (by constructor <;> assumption)
  have hsrcNeg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hsourceFull
  have htailPower : (fun u : ℝ => if u < 0 then
      (pastTailSourceVector H t hH0 hH1 ht0 ht1 : ℝ → ℝ) (-u) else 0) =ᵐ[volume]
      pastTailKernel H t := by
    have hextg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (pastPositiveExtension_ae (pastTailSourceVector H t hH0 hH1 ht0 ht1))
    filter_upwards [hsrcNeg, hextg] with u hu hv
    by_cases hu0 : u < 0
    · have hpos : -u ∈ Set.Ioi (0:ℝ) := by simp [hu0]
      have h1 : (pastPositiveExtension (pastTailSourceVector H t hH0 hH1 ht0 ht1) :
          ℝ → ℝ) (-u) = pastTailPower (H-1/2) t (-u) := by
        simpa [Function.comp_def, Set.indicator, hpos] using hu
      have h2 : (pastPositiveExtension (pastTailSourceVector H t hH0 hH1 ht0 ht1) :
          ℝ → ℝ) (-u) = (pastTailSourceVector H t hH0 hH1 ht0 ht1 : ℝ → ℝ) (-u) := by
        simpa [Function.comp_def, Set.indicator, hpos] using hv
      have heq := h2.symm.trans h1
      simp [pastTailKernel, hu0, heq]
    · simp [pastTailKernel, hu0]
  have hneg := (negativeSourceEmbedding_ae
      (pastTailSourceVector H t hH0 hH1 ht0 ht1)).trans htailPower
  have hadd : (positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) +
      negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1) : FullLineL2) =ᵐ[volume]
      (fun u => mvNPositiveKernel (H-1/2) t u + pastTailKernel H t u) := by
    have hcoeff := Lp.coeFn_add
      (positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1))
      (negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1))
    filter_upwards [hcoeff, hpos, hneg] with u hu hp hn
    change ((positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) +
      negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1) : FullLineL2) :
        ℝ → ℝ) u = _
    rw [hu]
    change (positiveSourceExtension (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) :
      ℝ → ℝ) u + (negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1) :
      ℝ → ℝ) u = _
    rw [hp, hn]
  exact hfull.trans (hsplit.trans hadd.symm)

/-! The direct-sum estimate used to combine the two actual source sides. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Sum the two nested finite source subspaces inside one common Hilbert space. -/
def combinedSourceFiltration (U V : ℕ → Submodule ℝ E) (n : ℕ) : Submodule ℝ E :=
  U n ⊔ V n

theorem combinedSourceFiltration_mono (U V : ℕ → Submodule ℝ E)
    (hU : ∀ n, U n ≤ U (n+1)) (hV : ∀ n, V n ≤ V (n+1)) :
    ∀ n, combinedSourceFiltration U V n ≤ combinedSourceFiltration U V (n+1) := by
  intro n
  apply sup_le
  · exact le_sup_of_le_left (hU n)
  · exact le_sup_of_le_right (hV n)

theorem combinedSourceFiltration_finiteDimensional (U V : ℕ → Submodule ℝ E)
    (hU : ∀ n, FiniteDimensional ℝ (U n))
    (hV : ∀ n, FiniteDimensional ℝ (V n)) (n : ℕ) :
    FiniteDimensional ℝ (combinedSourceFiltration U V n) := by
  letI := hU n
  letI := hV n
  exact Submodule.finiteDimensional_sup (U n) (V n)

theorem combinedSourceFiltration_finrank_le (U V : ℕ → Submodule ℝ E)
    (hU : ∀ n, FiniteDimensional ℝ (U n))
    (hV : ∀ n, FiniteDimensional ℝ (V n)) (n : ℕ) :
    Module.finrank ℝ (combinedSourceFiltration U V n) ≤
      Module.finrank ℝ (U n) + Module.finrank ℝ (V n) := by
  letI := hU n
  letI := hV n
  rw [combinedSourceFiltration, ← Submodule.finrank_sup_add_finrank_inf_eq]
  exact Nat.le_add_right _ _

/-- A pair of source-side approximants gives a full-line approximant in the
sum filtration, with the expected triangle bound. -/
theorem combinedSourceFiltration_approximation
    (U V : ℕ → Submodule ℝ E) (n : ℕ) (x y : E)
    (u : U n) (v : V n) :
    x + y - (u.1 + v.1) = (x-u.1) + (y-v.1) := by
  abel

/-! Concrete image filtrations and a reusable source-to-full-line adapter. -/

theorem finiteDimensional_map_submodule {F G : Type*}
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (f : F →ₗ[ℝ] G) (S : Submodule ℝ F) [FiniteDimensional ℝ S] :
    FiniteDimensional ℝ (S.map f) := by
  let fS : S →ₗ[ℝ] (S.map f) :=
    (f.comp S.subtype).codRestrict (S.map f) (fun x => ⟨x.1, x.2, rfl⟩)
  apply FiniteDimensional.of_surjective fS
  intro y
  rcases y.2 with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

def positiveFullLineFiltration (n : ℕ) : Submodule ℝ FullLineL2 :=
  (piecewisePolynomials 1 n).map positiveSourceExtension.toLinearMap

def pastFullLineFiltration (V : ℕ → Submodule ℝ PastPositiveL2) (n : ℕ) :
    Submodule ℝ FullLineL2 := V n |>.map negativeSourceEmbedding.toLinearMap

theorem positiveFullLineFiltration_mono :
    ∀ n, positiveFullLineFiltration n ≤ positiveFullLineFiltration (n+1) := by
  intro n
  exact Submodule.map_mono (piecewisePolynomials_le_succ 1 n)

theorem pastFullLineFiltration_mono (V : ℕ → Submodule ℝ PastPositiveL2)
    (hV : ∀ n, V n ≤ V (n+1)) :
    ∀ n, pastFullLineFiltration V n ≤ pastFullLineFiltration V (n+1) := by
  intro n
  exact Submodule.map_mono (hV n)

instance positiveFullLineFiltration_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (positiveFullLineFiltration n) := by
  unfold positiveFullLineFiltration
  exact finiteDimensional_map_submodule _ _

theorem pastFullLineFiltration_finiteDimensional
    (V : ℕ → Submodule ℝ PastPositiveL2)
    (hV : ∀ n, FiniteDimensional ℝ (V n)) (n : ℕ) :
    FiniteDimensional ℝ (pastFullLineFiltration V n) := by
  unfold pastFullLineFiltration
  exact finiteDimensional_map_submodule _ _

theorem positiveFullLineFiltration_finrank_le (n : ℕ) :
    Module.finrank ℝ (positiveFullLineFiltration n) ≤ 2^n := by
  unfold positiveFullLineFiltration
  calc
    Module.finrank ℝ ((piecewisePolynomials 1 n).map positiveSourceExtension.toLinearMap) ≤
        Module.finrank ℝ (piecewisePolynomials 1 n) :=
          Submodule.finrank_map_le _ _
    _ ≤ 1 * 2^n := piecewisePolynomials_finrank_le 1 n
    _ = 2^n := by simp

theorem pastFullLineFiltration_finrank_le
    (V : ℕ → Submodule ℝ PastPositiveL2)
    (hV : ∀ n, FiniteDimensional ℝ (V n)) (n : ℕ) :
    Module.finrank ℝ (pastFullLineFiltration V n) ≤ Module.finrank ℝ (V n) := by
  unfold pastFullLineFiltration
  exact Submodule.finrank_map_le _ _

/-- The positive causal source has a q=1 polynomial approximant with the sharp
`2^{-H n}` error exponent for every `0 < H < 1`. -/
theorem positiveMvNSourceVector_polynomial_approximation (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ t : ℝ, ∀ ht0 : 0 ≤ t, ∀ ht1 : t ≤ 1,
      ∃ u : piecewisePolynomials 1 n,
        ‖positiveMvNSourceVector H t hH0 hH1 ht0 ht1 - u.1‖ ≤
          Real.Gamma (H+1/2) * Real.sqrt C * ((2:ℝ)^(-H))^n := by
  obtain ⟨C,hC,hbound⟩ := polynomialProjection_residual_geometric
    (α:=H+1/2) (q:=1) (by norm_num) (by linarith) (by linarith)
  refine ⟨C,hC,?_⟩
  intro n t ht0 ht1
  let k := kernelVector (H+1/2) t (by linarith) ht0 ht1
  let γ := Real.Gamma (H+1/2)
  refine ⟨⟨γ • polynomialProjection 1 n k,
    (piecewisePolynomials 1 n).smul_mem γ
      ((piecewisePolynomials 1 n).starProjection_apply_mem k)⟩, ?_⟩
  have h := hbound n t ht0 ht1
  have hδsq : ((2:ℝ)^(-H))^2 =
      (2:ℝ)^(-(2*(H+1/2)-1)) := by
    calc
      ((2:ℝ)^(-H))^2 = Real.rpow (Real.rpow 2 (-H)) (2:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow 2 ((-H)*2) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-H) 2).symm
      _ = _ := by congr 1 <;> ring
  have hrate : ((2:ℝ)^(-H))^(2*n) = ((2:ℝ)^(-(2*(H+1/2)-1)))^n := by
    calc
      ((2:ℝ)^(-H))^(2*n) = (((2:ℝ)^(-H))^2)^n :=
        pow_mul ((2:ℝ)^(-H)) 2 n
      _ = _ := by rw [hδsq]
  have hnonneg : 0 ≤ ((2:ℝ)^(-H))^n := by positivity
  have hbound' : ‖k - polynomialProjection 1 n k‖^2 ≤
      C * (((2:ℝ)^(-H))^(2*n)) := by simpa [k, hrate] using h
  have hGamma : 0 ≤ γ := by dsimp [γ]; positivity
  have hnorm : ‖γ • k - γ • polynomialProjection 1 n k‖ ≤
      γ * Real.sqrt C * ((2:ℝ)^(-H))^n := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hGamma]
    have hrhs : 0 ≤ γ * Real.sqrt C * ((2:ℝ)^(-H))^n := by positivity
    apply (sq_le_sq₀ (mul_nonneg hGamma (norm_nonneg _)) hrhs).mp
    calc
      (γ * ‖k - polynomialProjection 1 n k‖)^2 ≤
          γ^2 * (C * ((2:ℝ)^(-H))^(2*n)) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hbound' (sq_nonneg γ)
      _ = (γ * Real.sqrt C * ((2:ℝ)^(-H))^n)^2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hC.le]
        ring
  simpa [positiveMvNSourceVector, γ, k, sub_smul] using hnorm

/-- Generic actual full-line approximation from independent positive and past
source approximants. This exposes the precise data needed from a concrete
past Taylor filtration without hiding the full-line feature in a premise. -/
theorem combinedSourceFiltration_add_mem (U V : Submodule ℝ E)
    {u v : E} (hu : u ∈ U) (hv : v ∈ V) : u+v ∈ U ⊔ V :=
  Submodule.add_mem_sup hu hv

/-- Combine actual positive-source polynomial and negative-source past-tail
approximants inside the full-line feature filtration. -/
theorem mvNNormalizedFeature_sum_filtration_approximation
    (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (V : ℕ → Submodule ℝ PastPositiveL2) (n : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u : piecewisePolynomials 1 n) (v : V n)
    (εpos εpast : ℝ) (hεp : 0 ≤ εpos) (hεv : 0 ≤ εpast)
    (hpos : ‖positiveMvNSourceVector H t hH0 hH1 ht0 ht1-u.1‖ ≤ εpos)
    (hpast : ‖pastTailSourceVector H t hH0 hH1 ht0 ht1-v.1‖ ≤ εpast) :
    ∃ z : combinedSourceFiltration
        (positiveFullLineFiltration) (pastFullLineFiltration V) n,
      ‖mvNNormalizedFeature H hH0 hH1 t ht0 ht1-z.1‖ ≤
        ‖mvNFullFeature (H-1/2) 1
          (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖⁻¹ *
          (εpos+εpast) := by
  let N := ‖mvNFullFeature (H-1/2) 1
    (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖
  have hNpos : 0 < N := by
    dsimp [N]
    exact mvNFullKernel_one_norm_pos (H-1/2)
      (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)
  let a := positiveSourceExtension (u.1)
  let b := negativeSourceEmbedding (v.1)
  let z : FullLineL2 := N⁻¹ • (a+b)
  have ha : a ∈ positiveFullLineFiltration n := by
    exact ⟨u.1,u.2,rfl⟩
  have hb : b ∈ pastFullLineFiltration V n := by
    exact ⟨v.1,v.2,rfl⟩
  have hz : z ∈ combinedSourceFiltration
      (positiveFullLineFiltration) (pastFullLineFiltration V) n := by
    exact (combinedSourceFiltration (positiveFullLineFiltration)
      (pastFullLineFiltration V) n).smul_mem N⁻¹
        (combinedSourceFiltration_add_mem _ _ ha hb)
  refine ⟨⟨z,hz⟩, ?_⟩
  have hdecomp := mvNFullFeature_eq_positive_add_past H t hH0 hH1 ht0 ht1
  have hposerr : ‖positiveSourceExtension
      (positiveMvNSourceVector H t hH0 hH1 ht0 ht1-u.1)‖ ≤ εpos := by
    rw [positiveSourceExtension_norm]
    exact hpos
  have hpasterr : ‖negativeSourceEmbedding
      (pastTailSourceVector H t hH0 hH1 ht0 ht1-v.1)‖ ≤ εpast := by
    rw [negativeSourceEmbedding_norm]
    exact hpast
  have hadd : ‖(positiveSourceExtension
      (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) +
      negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1)) -
      (a+b)‖ ≤ εpos+εpast := by
    have heq : (positiveSourceExtension
        (positiveMvNSourceVector H t hH0 hH1 ht0 ht1) +
        negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1)) -
        (a+b) = positiveSourceExtension
          (positiveMvNSourceVector H t hH0 hH1 ht0 ht1-u.1) +
          negativeSourceEmbedding (pastTailSourceVector H t hH0 hH1 ht0 ht1-v.1) := by
      dsimp [a,b]
      rw [map_sub, map_sub]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hposerr hpasterr)
  change ‖N⁻¹ • mvNFullFeature (H-1/2) t
      (mvNFullKernel_memLp hH0 hH1 ⟨ht0,ht1⟩) - N⁻¹ • (a+b)‖ ≤ N⁻¹*(εpos+εpast)
  rw [← smul_sub, hdecomp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hNpos.le)]
  exact mul_le_mul_of_nonneg_left hadd (inv_nonneg.mpr hNpos.le)

/-- The concrete past source filtration selected by the dyadic Taylor scheme. -/
def actualPastSourceFiltration (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (n : ℕ) : Submodule ℝ PastPositiveL2 :=
  actualPastTailSpan (H-1/2) (by linarith) (by linarith) n (n+1)

theorem actualPastSourceFiltration_mono (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    ∀ n, actualPastSourceFiltration H hH0 hH1 n ≤
      actualPastSourceFiltration H hH0 hH1 (n+1) := by
  intro n
  change actualPastTailSpan (H-1/2) (by linarith) (by linarith) n (n+1) ≤
    actualPastTailSpan (H-1/2) (by linarith) (by linarith) (n+1) ((n+1)+1)
  unfold actualPastTailSpan
  exact pastTailTaylorSpan_mono _ (Nat.le_succ n) (Nat.le_succ (n+1))

theorem actualPastSourceFiltration_finiteDimensional (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) (n : ℕ) :
    FiniteDimensional ℝ (actualPastSourceFiltration H hH0 hH1 n) := by
  change FiniteDimensional ℝ
    (actualPastTailSpan (H-1/2) (by linarith) (by linarith) n (n+1))
  unfold actualPastTailSpan pastTailTaylorSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem actualPastSourceFiltration_rank_bound (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ n,
      Module.rank ℝ (actualPastSourceFiltration H hH0 hH1 n) ≤
        ((A*2^n:ℕ):Cardinal) := by
  obtain ⟨A,hA,hbound⟩ := actualPastTailSpan_dyadic_rank_bound
    (H-1/2) (by linarith) (by linarith)
  refine ⟨A,hA,?_⟩
  intro n
  change Module.rank ℝ (actualPastTailSpan (H-1/2) (by linarith)
    (by linarith) n (n+1)) ≤ _
  exact hbound n

/-- Actual normalized two-sided MvN features have a uniform finite-rank
full-line approximation at their sharp scalar exponent `H`. -/
theorem mvNNormalizedFeature_actual_filtration_approximation (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ t : ℝ, ∀ ht0 : 0 ≤ t, ∀ ht1 : t ≤ 1,
      ∃ z ∈ combinedSourceFiltration positiveFullLineFiltration
          (pastFullLineFiltration (actualPastSourceFiltration H hH0 hH1)) n,
        ‖mvNNormalizedFeature H hH0 hH1 t ht0 ht1-z‖ ≤ C*((2:ℝ)^(-H))^n := by
  obtain ⟨Cp,hCp,hp⟩ := positiveMvNSourceVector_polynomial_approximation H hH0 hH1
  obtain ⟨Cv,hCv,hv⟩ := exists_actualPastTail_dyadic_approximation
    (H-1/2) (by linarith) (by linarith)
  let N := ‖mvNFullFeature (H-1/2) 1
    (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)‖
  let δ := (2:ℝ)^(-H)
  let C := N⁻¹*(Real.Gamma (H+1/2)*Real.sqrt Cp+Cv)
  have hNpos : 0 < N := by
    dsimp [N]
    exact mvNFullKernel_one_norm_pos (H-1/2)
      (mvNFullKernel_memLp hH0 hH1 ⟨by norm_num,by norm_num⟩)
  have hC : 0 < C := by
    dsimp [C]
    have hg : 0 < Real.Gamma (H+1/2) := by positivity
    positivity
  refine ⟨C,hC,?_⟩
  intro n t ht0 ht1
  obtain ⟨u,hu⟩ := hp n t ht0 ht1
  obtain ⟨v,hvspan,hverr⟩ := hv n t ht0 ht1
  have hVeq : actualPastSourceFiltration H hH0 hH1 n =
      actualPastTailSpan (H-1/2) (by linarith) (by linarith) n (n+1) := rfl
  have hv' : v ∈ actualPastSourceFiltration H hH0 hH1 n := by
    rw [hVeq]
    exact hvspan
  have htvec : pastTailSourceVector H t hH0 hH1 ht0 ht1 =
      pastTailParameterVector (H-1/2) (by linarith) (by linarith) t ht0 ht1 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp
      (pastTailPower_memLp_two (by linarith) (by linarith) ht0 ht1)).trans
        (MemLp.coeFn_toLp
          (pastTailPower_memLp_two (by linarith) (by linarith) ht0 ht1)).symm
  have hpow : (2:ℝ)^(-(H)*(n:ℝ)) = δ^n := by
    dsimp [δ]
    calc
      (2:ℝ)^((-H)*(n:ℝ)) = ((2:ℝ)^(-H))^(n:ℝ) :=
        Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-H) (n:ℝ)
      _ = ((2:ℝ)^(-H))^n := Real.rpow_natCast _ _
  have hHcast : -(H-1/2+1/2)*(n:ℝ) = -H*(n:ℝ) := by ring
  have hvRate : ‖pastTailParameterVector (H-1/2) (by linarith) (by linarith)
      t ht0 ht1-v‖ ≤ Cv*δ^n := by
    have hpow' : (2:ℝ)^(-(H-1/2+1/2)*(n:ℝ)) = δ^n := by
      rw [hHcast, hpow]
    rw [hpow'] at hverr
    exact hverr
  have hpastErr : ‖pastTailSourceVector H t hH0 hH1 ht0 ht1-v‖ ≤ Cv*δ^n := by
    rw [htvec]
    exact hvRate
  have hposErr : ‖positiveMvNSourceVector H t hH0 hH1 ht0 ht1-u.1‖ ≤
      Real.Gamma (H+1/2)*Real.sqrt Cp*δ^n := by
    simpa [δ] using hu
  obtain ⟨z,hzerr⟩ := mvNNormalizedFeature_sum_filtration_approximation
    H hH0 hH1 (actualPastSourceFiltration H hH0 hH1) n t ht0 ht1 u ⟨v,hv'⟩
    (Real.Gamma (H+1/2)*Real.sqrt Cp*δ^n) (Cv*δ^n)
    (by positivity) (by positivity) hposErr hpastErr
  refine ⟨z.1, z.2, ?_⟩
  dsimp [C, δ, N] at hzerr ⊢
  nlinarith [hzerr]

/-- The concrete normalized MvN source spaces have exponentially bounded
rank, with constants depending on H but not on the level. -/
theorem mvNNormalizedFeature_actual_filtration_rank (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ,
      Module.rank ℝ (combinedSourceFiltration positiveFullLineFiltration
        (pastFullLineFiltration (actualPastSourceFiltration H hH0 hH1)) n) ≤
        ((D*2^n:ℕ):Cardinal) := by
  obtain ⟨A,hA,hArank⟩ := actualPastSourceFiltration_rank_bound H hH0 hH1
  let V := actualPastSourceFiltration H hH0 hH1
  have hVfin : ∀ n, FiniteDimensional ℝ (V n) :=
    fun n => actualPastSourceFiltration_finiteDimensional H hH0 hH1 n
  have hPastFin : ∀ n, FiniteDimensional ℝ (pastFullLineFiltration V n) :=
    fun n => pastFullLineFiltration_finiteDimensional V hVfin n
  have hCombFin : ∀ n, FiniteDimensional ℝ
      (combinedSourceFiltration positiveFullLineFiltration
        (pastFullLineFiltration V) n) := by
    intro n
    exact combinedSourceFiltration_finiteDimensional
      positiveFullLineFiltration (pastFullLineFiltration V)
      (fun n => positiveFullLineFiltration_finiteDimensional n) hPastFin n
  let D := A+1
  refine ⟨D, by dsimp [D]; omega, ?_⟩
  intro n
  have hPastFinrank : Module.finrank ℝ (pastFullLineFiltration V n) ≤ A*2^n := by
    have h1 := pastFullLineFiltration_finrank_le V hVfin n
    have h2 := hArank n
    rw [← Module.finrank_eq_rank ℝ (V n)] at h2
    exact h1.trans (by exact_mod_cast h2)
  have hTotalFinrank : Module.finrank ℝ
      (combinedSourceFiltration positiveFullLineFiltration
        (pastFullLineFiltration V) n) ≤ (A+1)*2^n := by
    have hdim := combinedSourceFiltration_finrank_le
      positiveFullLineFiltration (pastFullLineFiltration V)
      (fun n => positiveFullLineFiltration_finiteDimensional n) hPastFin n
    have hpos := positiveFullLineFiltration_finrank_le n
    have hAcast : 1 ≤ (A:ℝ) := by exact_mod_cast hA
    have hsum : (2:ℝ)^n + (A:ℝ)*(2:ℝ)^n ≤
        ((A+1:ℕ):ℝ)*(2:ℝ)^n := by
      have hpow : 0 ≤ (2:ℝ)^n := by positivity
      push_cast
      nlinarith
    calc
      Module.finrank ℝ (combinedSourceFiltration positiveFullLineFiltration
          (pastFullLineFiltration V) n) ≤
          Module.finrank ℝ (positiveFullLineFiltration n) +
            Module.finrank ℝ (pastFullLineFiltration V n) := hdim
      _ ≤ 2^n + A*2^n := Nat.add_le_add hpos hPastFinrank
      _ ≤ (A+1)*2^n := by exact_mod_cast hsum
  rw [← Module.finrank_eq_rank ℝ
    (combinedSourceFiltration positiveFullLineFiltration
      (pastFullLineFiltration V) n)]
  exact_mod_cast hTotalFinrank

/-- The exact scalar full-line filtration consumed by the fractional-sheet
graded Gaussian reverse argument. -/
def actualMvNFiltration (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    ℕ → Submodule ℝ FullLineL2 :=
  combinedSourceFiltration positiveFullLineFiltration
    (pastFullLineFiltration (actualPastSourceFiltration H hH0 hH1))

theorem actualMvNFiltration_finiteDimensional (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) (n : ℕ) :
    FiniteDimensional ℝ (actualMvNFiltration H hH0 hH1 n) := by
  exact combinedSourceFiltration_finiteDimensional positiveFullLineFiltration
    (pastFullLineFiltration (actualPastSourceFiltration H hH0 hH1))
    (fun n => positiveFullLineFiltration_finiteDimensional n)
    (fun n => pastFullLineFiltration_finiteDimensional
      (actualPastSourceFiltration H hH0 hH1)
      (fun n => actualPastSourceFiltration_finiteDimensional H hH0 hH1 n) n) n

theorem actualMvNFiltration_mono (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∀ n, actualMvNFiltration H hH0 hH1 n ≤ actualMvNFiltration H hH0 hH1 (n+1) := by
  apply combinedSourceFiltration_mono
    positiveFullLineFiltration (pastFullLineFiltration
      (actualPastSourceFiltration H hH0 hH1))
  · exact positiveFullLineFiltration_mono
  · exact pastFullLineFiltration_mono (actualPastSourceFiltration H hH0 hH1)
      (actualPastSourceFiltration_mono H hH0 hH1)

/-- The base grade is nonempty because the positive source filtration contains
the extension of a nonzero constant-on-the-cube source vector. -/
theorem actualMvNFiltration_grade_zero_nonempty (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    Nonempty (GradeIndex (actualMvNFiltration H hH0 hH1) 0) := by
  let U := actualMvNFiltration H hH0 hH1
  letI : FiniteDimensional ℝ (U 0) :=
    actualMvNFiltration_finiteDimensional H hH0 hH1 0
  have hsource : 0 < Module.finrank ℝ (piecewisePolynomials 1 0) :=
    piecewisePolynomials_finrank_pos (by norm_num) 0
  letI : Nontrivial (piecewisePolynomials 1 0) :=
    Module.nontrivial_of_finrank_pos hsource
  obtain ⟨x,hx⟩ := exists_ne (0 : piecewisePolynomials 1 0)
  have himage : positiveSourceExtension (x : UnitL2) ≠ 0 := by
    intro hz
    have hnorm : ‖positiveSourceExtension (x : UnitL2)‖ = 0 := by
      rw [hz, norm_zero]
    rw [positiveSourceExtension_norm] at hnorm
    exact hx (Subtype.ext (norm_eq_zero.mp hnorm))
  have hmem : positiveSourceExtension (x : UnitL2) ∈ U 0 := by
    change positiveSourceExtension (x : UnitL2) ∈
      positiveFullLineFiltration 0 ⊔
        pastFullLineFiltration (actualPastSourceFiltration H hH0 hH1) 0
    exact Submodule.mem_sup_left ⟨x.1,x.2,rfl⟩
  letI : Nontrivial (U 0) := ⟨⟨0, (U 0).zero_mem⟩,
    ⟨positiveSourceExtension (x : UnitL2),hmem⟩, by
      intro h
      have heq : 0 = positiveSourceExtension (x : UnitL2) :=
        congrArg (fun y : U 0 => (y : FullLineL2)) h
      exact himage heq.symm⟩
  have hdim : 0 < Module.finrank ℝ (U 0) := Module.finrank_pos
  exact ⟨⟨0, hdim⟩⟩

theorem actualMvNFiltration_rank_bound (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ,
      Module.rank ℝ (actualMvNFiltration H hH0 hH1 n) ≤ ((D*2^n:ℕ):Cardinal) := by
  obtain ⟨D,hD,hRank⟩ := mvNNormalizedFeature_actual_filtration_rank H hH0 hH1
  refine ⟨D,hD,?_⟩
  intro n
  have hh := hRank n
  change Module.rank ℝ (actualMvNFiltration H hH0 hH1 n) ≤
    ((D*2^n:ℕ):Cardinal)
  exact hh

theorem actualMvNFiltration_grade_card_bound (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ g : ℕ,
      Fintype.card (GradeIndex (actualMvNFiltration H hH0 hH1) g) ≤ A*2^g := by
  obtain ⟨D,hD,hRank⟩ := actualMvNFiltration_rank_bound H hH0 hH1
  let U := actualMvNFiltration H hH0 hH1
  have hfinite : ∀ n, FiniteDimensional ℝ (U n) :=
    fun n => actualMvNFiltration_finiteDimensional H hH0 hH1 n
  have hfiniteRank (n : ℕ) : Module.finrank ℝ (U n) ≤ D*2^n := by
    have hh := hRank n
    rw [← Module.finrank_eq_rank ℝ (U n)] at hh
    exact_mod_cast hh
  let A := 2*D
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro g
  cases g with
  | zero =>
      have hcard : Fintype.card (GradeIndex U 0) =
          Module.finrank ℝ (U 0) := by simp [GradeIndex]
      rw [hcard]
      have hfin := hfiniteRank 0
      dsimp [A]
      simp only [pow_zero, Nat.mul_one]
      omega
  | succ g =>
      letI := hfinite (g+1)
      have hinc : increment U g ≤ U (g+1) := inf_le_left
      have hdim : Module.finrank ℝ (increment U g) ≤
          Module.finrank ℝ (U (g+1)) := Submodule.finrank_mono hinc
      have hcard : Fintype.card (GradeIndex U (g+1)) =
          Module.finrank ℝ (increment U g) := by simp [GradeIndex]
      rw [hcard]
      have hfin := hfiniteRank (g+1)
      dsimp [A]
      calc
        Module.finrank ℝ (increment U g) ≤ D*2^(g+1) := hdim.trans hfin
        _ ≤ 2*D*2^(g+1) := by
          exact Nat.mul_le_mul_right (2^(g+1)) (by omega)

/-- Orthogonal projection onto the concrete full-line filtration preserves the
uniform sharp `H`-rate of the actual normalized axis features. -/
theorem normalizedAxis_actualMvN_projection_rate (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ t : UnitInterval,
      (letI : FiniteDimensional ℝ (actualMvNFiltration H hH0 hH1 n) :=
        actualMvNFiltration_finiteDimensional H hH0 hH1 n
       ‖normalizedAxis H hH0 hH1 t -
        (actualMvNFiltration H hH0 hH1 n).starProjection
          (normalizedAxis H hH0 hH1 t)‖^2 ≤
        C*((2:ℝ)^(-2*H))^n) := by
  obtain ⟨C,hC,happrox⟩ :=
    mvNNormalizedFeature_actual_filtration_approximation H hH0 hH1
  refine ⟨C^2, by positivity, ?_⟩
  intro n t
  let U := actualMvNFiltration H hH0 hH1
  let x := normalizedAxis H hH0 hH1 t
  let δ := (2:ℝ)^(-H)
  letI : FiniteDimensional ℝ (U n) :=
    actualMvNFiltration_finiteDimensional H hH0 hH1 n
  obtain ⟨z,hz,hzerr⟩ := happrox n t.val t.property.1 t.property.2
  have hbest : ‖x-(U n).starProjection x‖ ≤ ‖x-z‖ := by
    rw [Submodule.starProjection_minimal (U := U n) x]
    have hbdd : BddBelow (Set.range (fun y : U n => ‖x-(y:FullLineL2)‖)) :=
      ⟨0, Set.forall_mem_range.mpr (fun y => norm_nonneg _)⟩
    exact ciInf_le hbdd ⟨z,hz⟩
  have hδsq : δ^2 = (2:ℝ)^(-2*H) := by
    dsimp [δ]
    calc
      ((2:ℝ)^(-H))^2 = Real.rpow (Real.rpow 2 (-H)) (2:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow 2 ((-H)*2) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-H) 2).symm
      _ = _ := by congr 1 <;> ring
  have hpow : (δ^n)^2 = δ^(2*n) := by
    calc
      (δ^n)^2 = δ^(n*2) := (pow_mul δ n 2).symm
      _ = δ^(2*n) := by congr 1 <;> omega
  have hrate : δ^(2*n) = ((2:ℝ)^(-2*H))^n := by
    calc
      δ^(2*n) = (δ^2)^n := pow_mul δ 2 n
      _ = _ := by rw [hδsq]
  have hrhs : 0 ≤ C*δ^n := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg _) hrhs).2 hzerr
  have hsq' : ‖x-(U n).starProjection x‖^2 ≤ C^2*δ^(2*n) := by
    calc
      ‖x-(U n).starProjection x‖^2 ≤ ‖x-z‖^2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hbest 2
      _ ≤ (C*δ^n)^2 := hsq
      _ = C^2*δ^(2*n) := by rw [mul_pow, hpow]
  have hexp : -2*H = -(2*H) := by ring
  have hrpow : (2:ℝ)^(-2*H) = (2:ℝ)^(-(2*H)) :=
    congrArg (fun z : ℝ => (2:ℝ)^z) hexp
  have hrate' : δ^(2*n) = ((2:ℝ)^(-(2*H)))^n := by
    calc
      δ^(2*n) = ((2:ℝ)^(-2*H))^n := hrate
      _ = ((2:ℝ)^(-(2*H)))^n := by rw [hrpow]
  calc
    ‖x-(U n).starProjection x‖^2 ≤ C^2*((2:ℝ)^(-2*H))^n := by
      calc
        ‖x-(U n).starProjection x‖^2 ≤ C^2*δ^(2*n) := hsq'
        _ = C^2*((2:ℝ)^(-(2*H)))^n := by rw [hrate']
        _ = C^2*((2:ℝ)^(-2*H))^n := by rw [← hrpow]

end BrownianSharp.AlignmentGaussianMvNFullLineFiltration
