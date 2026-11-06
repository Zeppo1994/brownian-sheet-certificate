import BrownianSharp.AlignmentPaperBrownianEntropyRoute
import BrownianSharp.AlignmentPaperFractional
import BrownianSharp.AlignmentPaperGaussianPathLaws

/-!
# Universe-polymorphic small-deviation statements for the sheets

Theorem 1.1 (Brownian sheet), Theorem 5.2 (fractional and integrated sheets)
for arbitrary probability spaces `Ω : Type u`. A realization is transported to
the canonical one on `(C(cube, ℝ), P.map B.path)`, whose path is the identity;
the Gaussian, mean and covariance conditions are statements about the path law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
namespace BrownianSharp.AlignmentPaperSheetUniverse

open BrownianSharp.AlignmentGaussianRates BrownianSharp.Latest
open BrownianSharp.AlignmentPaperGaussianPathLaws

universe u

/-- Theorem 1.1 for every probability space. -/
def BrownianTwoSidedStatementU : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C ε₀ : ℝ,
    0<c ∧ 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0<ε → ε≤ε₀ →
        c*sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ∧
        -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ≤ C*sharpRate d ε

/-- Theorem 5.2 (fractional sheet) for every probability space. -/
def FractionalSheetStatementU : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ H : Fin d → ℝ, (∀ i, 0<H i ∧ H i<1) →
    ∀ h : ℝ, ∀ ν : ℕ, 2≤ν → minimumMultiplicity H h ν →
    ∃ c C ε₀ : ℝ, 0<c ∧ 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : FractionalBrownianSheetOnCube d Ω P), B.H=H →
      ∀ ε : ℝ, 0<ε → ε≤ε₀ →
        c*smallBallRate h⁻¹ ((ν-1:ℕ)+(ν:ℝ)/(2*h)) ε ≤
          -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ∧
        -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ≤
          C*smallBallRate h⁻¹ ((ν-1:ℕ)+(ν:ℝ)/(2*h)) ε

/-- Theorem 5.2 (integrated sheet) for every probability space. -/
def IntegratedSheetStatementU : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ m : ℕ,
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          c * smallBallRate (2 / (2 * (m : ℝ) + 1))
            ((d - 1 : ℕ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε ≤
              -Real.log (P.real
                {ω | ‖integrateSheetPath (fun _ : Fin d => m)
                    (B.path ω)‖ ≤ ε}) ∧
          -Real.log (P.real
            {ω | ‖integrateSheetPath (fun _ : Fin d => m)
                (B.path ω)‖ ≤ ε}) ≤
              C * smallBallRate (2 / (2 * (m : ℝ) + 1))
                ((d - 1 : ℕ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε

/-- Small-ball probabilities of a measurable functional of the path depend only
on the path law. -/
theorem real_eq_map {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → C(BrownianCubeAnchor d, ℝ)) (hF : Measurable F)
    (φ : C(BrownianCubeAnchor d, ℝ) → C(BrownianCubeAnchor d, ℝ))
    (hφ : Measurable φ) (ε : ℝ) :
    P.real {ω | ‖φ (F ω)‖ ≤ ε} = (P.map F).real {f | ‖φ f‖ ≤ ε} := by
  have hs : MeasurableSet {f : C(BrownianCubeAnchor d, ℝ) | ‖φ f‖ ≤ ε} :=
    measurableSet_le (measurable_norm.comp hφ) measurable_const
  rw [Measure.real, Measure.real, Measure.map_apply hF hs]
  rfl

/-- The canonical Type-0 realization of a Brownian sheet: same path law. -/
def BrownianSheetCanonical {d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P) :
    BrownianSheetOnCube d C(BrownianCubeAnchor d, ℝ) (P.map B.path) :=
  let h := isCenteredPathLaw_map B.path B.measurable_path B.gaussian B.mean_zero
    (fun x y => ∏ i, min (x.val i) (y.val i)) B.covariance
  ⟨id, measurable_id, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The canonical Type-0 realization of a fractional sheet: same path law. -/
def FractionalSheetCanonical {d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : FractionalBrownianSheetOnCube d Ω P) :
    FractionalBrownianSheetOnCube d C(BrownianCubeAnchor d, ℝ) (P.map B.path) :=
  let h := isCenteredPathLaw_map B.path B.measurable_path B.gaussian B.mean_zero
    (fractionalSheetCovariance B.H) B.covariance
  ⟨B.H, B.hH, id, measurable_id, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Theorem 1.1 for `Ω : Type u`, from the Type-0 case. -/
theorem brownianTwoSided_certified : BrownianTwoSidedStatementU.{u} := by
  intro d hd
  obtain ⟨c, C, ε₀, hc, hC, hε, hεe, h⟩ :=
    AlignmentPaperBrownianEntropyRoute.brownianTwoSided_paperRoute d hd
  refine ⟨c, C, ε₀, hc, hC, hε, hεe, fun Ω _ P _ B ε hε0 hle => ?_⟩
  have e : P.real {ω | ‖B.path ω‖ ≤ ε} = (P.map B.path).real {f | ‖f‖ ≤ ε} :=
    real_eq_map P B.path B.measurable_path id measurable_id ε
  rw [e]
  exact h _ (P.map B.path) (BrownianSheetCanonical B) ε hε0 hle

/-- Theorem 5.2 (fractional sheet) for `Ω : Type u`, from the Type-0 case. -/
theorem fractionalSheet_certified : FractionalSheetStatementU.{u} := by
  intro d hd H hH h ν hν hm
  obtain ⟨c, C, ε₀, hc, hC, hε, hεe, hb⟩ :=
    AlignmentPaperFractional.paperFractionalSheet_certified d hd H hH h ν hν hm
  refine ⟨c, C, ε₀, hc, hC, hε, hεe, fun Ω _ P _ B hBH ε hε0 hle => ?_⟩
  have e : P.real {ω | ‖B.path ω‖ ≤ ε} = (P.map B.path).real {f | ‖f‖ ≤ ε} :=
    real_eq_map P B.path B.measurable_path id measurable_id ε
  rw [e]
  exact hb _ (P.map B.path) (FractionalSheetCanonical B) hBH ε hε0 hle

/-- Theorem 5.2 (integrated sheet) for `Ω : Type u`, from the Type-0 case. -/
theorem integratedSheet_certified : IntegratedSheetStatementU.{u} := by
  intro d hd m
  obtain ⟨c, C, ε₀, hc, hC, hε, hεe, h⟩ :=
    AlignmentPaperFractional.paperIntegratedSheet_certified d hd m
  refine ⟨c, C, ε₀, hc, hC, hε, hεe, fun Ω _ P _ B ε hε0 hle => ?_⟩
  have e : P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m) (B.path ω)‖ ≤ ε} =
      (P.map B.path).real {f | ‖integrateSheetPath (fun _ : Fin d => m) f‖ ≤ ε} :=
    real_eq_map P B.path B.measurable_path _ (integrateSheetPath_continuous _).measurable ε
  rw [e]
  exact h _ (P.map B.path) (BrownianSheetCanonical B) ε hε0 hle

end BrownianSharp.AlignmentPaperSheetUniverse
