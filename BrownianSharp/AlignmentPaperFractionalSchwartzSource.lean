import BrownianSharp.AlignmentPaperFractionalFourierMultiplier
import BrownianSharp.AlignmentPaperContinuumGenericBump
import BrownianSharp.SmoothAtom
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Exact real compact smooth bump -> complex Schwartz source translation for
the manuscript fractional Fourier proof. Derivative orders and values are
identified, not replaced by an abstract source assumption. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace BrownianSharp.AlignmentPaperFractionalSchwartzSource

open BrownianSharp.AlignmentPaperFractionalFourierMultiplier

/-- Complexification preserves compact support. -/
theorem complexify_hasCompactSupport {F : ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (fun x => (F x : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact hF
  intro x hx
  apply subset_closure
  change (F x : ℂ) ≠ 0 at hx
  change F x ≠ 0
  exact fun heq => hx (by rw [heq]; rfl)

def realCompactSchwartz (F : ℝ → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hcompact : HasCompactSupport F) : 𝓢(ℝ,ℂ) :=
  (complexify_hasCompactSupport hcompact).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hF)

@[simp] theorem realCompactSchwartz_apply (F : ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hcompact : HasCompactSupport F) (x : ℝ) :
    realCompactSchwartz F hF hcompact x = (F x : ℂ) := rfl

theorem deriv_complexify {F : ℝ → ℝ} (hF : Differentiable ℝ F) (x : ℝ) :
    deriv (fun y => (F y : ℂ)) x = ((deriv F x : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hF x).hasDerivAt).deriv
  change deriv (Complex.ofRealCLM ∘ F) x = Complex.ofRealCLM (deriv F x)
  exact h

/-- The qth Schwartz directional derivative is exactly the complexification
of the qth real derivative used in the Riemann--Liouville preimage. -/
theorem iteratedLineDerivative_realCompactSchwartz (F : ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hcompact : HasCompactSupport F)
    (q : ℕ) (x : ℝ) :
    iteratedLineDerivative q (realCompactSchwartz F hF hcompact) x =
      ((iteratedDeriv q F x : ℝ) : ℂ) := by
  induction q generalizing x with
  | zero => simp [iteratedLineDerivative]
  | succ q ih =>
    rw [iteratedLineDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
    have hfun : ((iteratedLineDerivative q
        (realCompactSchwartz F hF hcompact) : 𝓢(ℝ,ℂ)) : ℝ → ℂ) =
        fun y => ((iteratedDeriv q F y : ℝ) : ℂ) := funext ih
    rw [hfun, deriv_complexify]
    · rw [iteratedDeriv_succ]
    · have hs : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv q F) := by
        simpa only [iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv q hF
      exact hs.differentiable (by simp)

theorem smoothAtom_hasCompactSupport : HasCompactSupport smoothAtom := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  intro x hx
  change smoothAtom x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (smoothAtom_support x (Or.inl (not_le.mp h).le))
  · by_contra h
    exact hx (smoothAtom_support x (Or.inr (not_le.mp h).le))

def smoothAtomSchwartz : 𝓢(ℝ,ℂ) :=
  realCompactSchwartz smoothAtom smoothAtom_contDiff smoothAtom_hasCompactSupport

@[simp] theorem smoothAtomSchwartz_apply (x : ℝ) :
    smoothAtomSchwartz x = (smoothAtom x : ℂ) := rfl

end BrownianSharp.AlignmentPaperFractionalSchwartzSource
