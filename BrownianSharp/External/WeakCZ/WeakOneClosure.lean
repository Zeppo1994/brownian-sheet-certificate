import BrownianSharp.AlignmentPaperWeakStrongInterpolation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Distributional assembly of actual good/bad decompositions. The concrete
CZ construction must supply the displayed moment and exceptional-set bounds. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace BrownianSharp.External.WeakCZ
open BrownianSharp.AlignmentPaperWeakStrongInterpolation

theorem norm_tail_le_first_moment {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (μ : Measure α) (g : α → E)
    (hg : AEStronglyMeasurable g μ) {t : ℝ} (ht : 0 < t) :
    μ {x | t < ‖g x‖} ≤ (∫⁻ x, ‖g x‖ₑ ∂μ) / ENNReal.ofReal t := by
  have hm : AEMeasurable (fun x => ‖g x‖ₑ) μ := by
    simpa only [ofReal_norm] using hg.norm.aemeasurable.ennreal_ofReal
  apply (measure_mono (show {x | t < ‖g x‖} ⊆
      {x | ENNReal.ofReal t ≤ ‖g x‖ₑ} from ?_)).trans
    (meas_ge_le_lintegral_div hm (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top)
  intro x hx
  change t < ‖g x‖ at hx
  change ENNReal.ofReal t ≤ ‖g x‖ₑ
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hx.le

/-- A threshold-t good square-moment bound and an off-exception bad L1 bound
produce one uniform weak-one constant. This is an internal assembly lemma,
not a substitute for the concrete Calderón–Zygmund decomposition. -/
theorem weak_one_of_good_bad_bounds {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (μ : Measure α) (F G B : α → E)
    (exception : Set α) (hexception : MeasurableSet exception)
    (hG : AEStronglyMeasurable G μ) (hB : AEStronglyMeasurable B μ)
    (hdecomp : ∀ x, F x = G x + B x)
    {t Ce Cg Cb : ℝ} (ht : 0 < t)
    (hCe : 0 ≤ Ce) (hCg : 0 ≤ Cg) (hCb : 0 ≤ Cb) (I : ENNReal)
    (hEbound : μ exception ≤ ENNReal.ofReal (Ce/t)*I)
    (hGbound : (∫⁻ x, ENNReal.ofReal (‖G x‖^2) ∂μ) ≤
      ENNReal.ofReal (Cg*t)*I)
    (hBbound : (∫⁻ x in exceptionᶜ, ‖B x‖ₑ ∂μ) ≤ ENNReal.ofReal Cb*I) :
    μ {x | t < ‖F x‖} ≤ ENNReal.ofReal ((Ce+4*Cg+2*Cb)/t)*I := by
  let B₀ : α → E := exceptionᶜ.indicator B
  have hB₀ : AEStronglyMeasurable B₀ μ := hB.indicator hexception.compl
  have hB₀int : (∫⁻ x, ‖B₀ x‖ₑ ∂μ) =
      ∫⁻ x in exceptionᶜ, ‖B x‖ₑ ∂μ := by
    rw [← lintegral_indicator hexception.compl]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ exceptionᶜ <;> simp [B₀, hx]
  have hsubset : {x | t < ‖F x‖} ⊆ exception ∪
      ({x | t/2 < ‖G x‖} ∪ {x | t/2 < ‖B₀ x‖}) := by
    intro x hx
    change t < ‖F x‖ at hx
    by_cases hex : x ∈ exception
    · exact Or.inl hex
    · apply Or.inr
      by_contra hn
      have hn' : ‖G x‖ ≤ t/2 ∧ ‖B₀ x‖ ≤ t/2 := by
        simpa only [mem_union,mem_setOf_eq,not_or,not_lt] using hn
      have hBvalue : B₀ x = B x := by simp [B₀,hex]
      have hnorm := norm_add_le (G x) (B x)
      rw [← hdecomp x] at hnorm
      rw [hBvalue] at hn'
      linarith
  have hhalf : 0 < t/2 := by positivity
  have hgTail : μ {x | t/2 < ‖G x‖} ≤ ENNReal.ofReal (4*Cg/t)*I := by
    calc
      _ ≤ (∫⁻ x, ENNReal.ofReal (‖G x‖^2) ∂μ) /
          ENNReal.ofReal ((t/2)^2) := norm_tail_le_squared_moment μ hG hhalf
      _ ≤ (ENNReal.ofReal (Cg*t)*I) / ENNReal.ofReal ((t/2)^2) := by gcongr
      _ = ENNReal.ofReal ((Cg*t)/(t/2)^2)*I := by
        rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hhalf)]
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by
        congr 2
        field_simp
        ring
  have hbTail : μ {x | t/2 < ‖B₀ x‖} ≤ ENNReal.ofReal (2*Cb/t)*I := by
    calc
      _ ≤ (∫⁻ x, ‖B₀ x‖ₑ ∂μ)/ENNReal.ofReal (t/2) :=
        norm_tail_le_first_moment μ B₀ hB₀ hhalf
      _ ≤ (ENNReal.ofReal Cb*I)/ENNReal.ofReal (t/2) := by
        rw [hB₀int]
        gcongr
      _ = ENNReal.ofReal (Cb/(t/2))*I := by
        rw [ENNReal.ofReal_div_of_pos hhalf]
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by congr 2; ring
  calc
    _ ≤ μ (exception ∪ ({x | t/2 < ‖G x‖} ∪ {x | t/2 < ‖B₀ x‖})) :=
      measure_mono hsubset
    _ ≤ μ exception + (μ {x | t/2 < ‖G x‖} + μ {x | t/2 < ‖B₀ x‖}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (Ce/t)*I +
        (ENNReal.ofReal (4*Cg/t)*I + ENNReal.ofReal (2*Cb/t)*I) :=
      add_le_add hEbound (add_le_add hgTail hbTail)
    _ = _ := by
      rw [← add_mul, ← add_mul,
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 4*Cg/t) (by positivity : 0 ≤ 2*Cb/t),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ Ce/t) (by positivity : 0 ≤ 4*Cg/t+2*Cb/t)]
      congr 2
      ring

end BrownianSharp.External.WeakCZ
