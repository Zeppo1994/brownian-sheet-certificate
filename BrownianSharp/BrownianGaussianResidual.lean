import BrownianSharp.BrownianHaarCovariance

/-! A finite-dimensional Gaussian block-independence bridge.  The exact
critical projection Gram matrix remains an explicit deterministic input; this
module derives residual independence from that Gram matrix and joint
Gaussianity, rather than assuming independence of the residual. -/

open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace HaarQuarter

/-- If a finite orthonormal family `e` has diagonal cross-Gram with a family
`v`, then the isonormal coordinates of `e` are independent of the Gaussian
residual coordinates `W(vᵢ - cᵢ eᵢ)`.  A single joint Gaussian field indexed
by `Sum I I` supplies the required joint law for both blocks. -/
theorem isonormal_projectionResidual_indepFun
    {H Ω I : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω (Sum I I) P)
    (e v : I → H) (c : I → ℝ)
    (heorth : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (hcross : ∀ i j, ⟪e i, v j⟫ = if i = j then c j else 0) :
    IndepFun (fun ω i => W.eval (e i) ω)
      (fun ω j => W.eval (v j - c j • e j) ω) P := by
  let vAll : Sum I I → H := Sum.elim e (fun j => v j - c j • e j)
  have hjoint := W.jointlyGaussian vAll
  have hblocks : HasGaussianLaw
      (fun ω => (fun i => W.eval (e i) ω,
        fun j => W.eval (v j - c j • e j) ω)) P := by
    let split := (LinearEquiv.sumArrowLequivProdArrow I I ℝ ℝ).toContinuousLinearEquiv
    have hmap := hjoint.map_equiv split
    have heq : (fun ω => split (fun k => W.eval (vAll k) ω)) =
        (fun ω => (fun i => W.eval (e i) ω,
          fun j => W.eval (v j - c j • e j) ω)) := by
      funext ω
      apply Prod.ext
      · funext i
        simp [split, vAll]
      · funext j
        simp [split, vAll]
    rw [← heq]
    exact hmap
  apply hblocks.indepFun_of_covariance_eval
  intro i j
  rw [W.covariance_eq_inner]
  rw [inner_sub_right, inner_smul_right, hcross i j, heorth i j]
  by_cases hij : i = j <;> simp [hij]

end HaarQuarter
