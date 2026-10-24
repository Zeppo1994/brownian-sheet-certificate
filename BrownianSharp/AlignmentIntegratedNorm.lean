import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.BrownianSheetCopyDifferenceLaw

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators
namespace BrownianSharp.AlignmentIntegratedNorm
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentGaussianBochner

theorem iterateCoordinatePath_norm_le_factorial {d : ℕ} (i : Fin d)
    (n : ℕ) (f : C(BrownianCubeAnchor d,ℝ)) :
    ‖iterateCoordinatePath i n f‖ ≤ ((n.factorial:ℝ)⁻¹)*‖f‖ := by
  cases n with
  | zero => simp [iterateCoordinatePath]
  | succ n =>
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    rw [iterateCoordinatePath_eq_normalizedPower]
    let w : ℝ→ℝ := fun u => (n.factorial:ℝ)⁻¹*(x.val i-u)^n
    let F : ℝ→ℝ := fun u => brownianCubeGlobalExtension f (Function.update x.val i u)
    have hw : Continuous w := by dsimp [w]; fun_prop
    have hF : Continuous F := by
      dsimp [F]
      exact (brownianCubeGlobalExtension f).continuous.comp (continuous_const.update i continuous_id)
    have hi : IntegrableOn (fun u => w u*F u) (Set.Ioc 0 (x.val i)) volume :=
      ((hw.mul hF).continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hb : IntegrableOn (fun u => w u*‖f‖) (Set.Ioc 0 (x.val i)) volume :=
      ((hw.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hw0 : ∀u∈Set.Ioc 0 (x.val i),0≤w u := by
      intro u hu
      dsimp [w]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (pow_nonneg (sub_nonneg.mpr hu.2) _)
    calc
      ‖∫ u in Set.Ioc 0 (x.val i), w u*F u‖ ≤
          ∫ u in Set.Ioc 0 (x.val i), ‖w u*F u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioc 0 (x.val i), w u*‖f‖ := by
        apply setIntegral_mono_on hi.norm hb measurableSet_Ioc
        intro u hu
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hw0 u hu)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hw0 u hu)
      _ = ((n+1).factorial:ℝ)⁻¹*(x.val i)^(n+1)*‖f‖ := by
        rw [integral_mul_const, ← intervalIntegral.integral_of_le (x.property i).1]
        dsimp [w]
        rw [intervalIntegral_normalizedPower_succ]
        simp
      _ ≤ ((n+1).factorial:ℝ)⁻¹*‖f‖ := by
        have hxpow : (x.val i)^(n+1)≤1 := pow_le_one₀ (x.property i).1 (x.property i).2
        calc
          _ ≤ ((n+1).factorial:ℝ)⁻¹*1*‖f‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hxpow (by positivity)) (norm_nonneg f)
          _ = _ := by ring

theorem fold_integrate_norm_le {d : ℕ} (m : Fin d→ℕ) (L : List (Fin d))
    (f : C(BrownianCubeAnchor d,ℝ)) :
    ‖L.foldl (fun g i => iterateCoordinatePath i (m i) g) f‖ ≤
      (L.map (fun i => ((m i).factorial:ℝ)⁻¹)).prod * ‖f‖ := by
  induction L generalizing f with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldl_cons,List.map_cons,List.prod_cons]
    calc
      _ ≤ (L.map (fun j => ((m j).factorial:ℝ)⁻¹)).prod *
          ‖iterateCoordinatePath i (m i) f‖ := ih _
      _ ≤ (L.map (fun j => ((m j).factorial:ℝ)⁻¹)).prod *
          (((m i).factorial:ℝ)⁻¹*‖f‖) := by
        apply mul_le_mul_of_nonneg_left (iterateCoordinatePath_norm_le_factorial i (m i) f)
        apply List.prod_nonneg
        intro a ha
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
        positivity
      _ = _ := by ring

theorem integrateSheetPath_norm_le_factorials {d : ℕ} (m : Fin d→ℕ)
    (f : C(BrownianCubeAnchor d,ℝ)) :
    ‖integrateSheetPath m f‖ ≤ (∏ i,((m i).factorial:ℝ)⁻¹)*‖f‖ := by
  have h := fold_integrate_norm_le m Finset.univ.toList f
  simpa only [integrateSheetPath,Finset.prod_map_toList] using h


theorem integrateSheetPath_factor_pos {d : ℕ} (m : Fin d→ℕ) :
    0 < ∏ i,((m i).factorial:ℝ)⁻¹ := by
  apply Finset.prod_pos
  intro i _
  positivity

theorem integrated_smallBall_mass_ge {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
    (m : Fin d→ℕ) (ε : ℝ) :
    P.real {ω | ‖B.path ω‖ ≤ ε/(∏ i,((m i).factorial:ℝ)⁻¹)} ≤
      P.real {ω | ‖integrateSheetPath m (B.path ω)‖≤ε} := by
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  have hF := integrateSheetPath_factor_pos m
  calc
    ‖integrateSheetPath m (B.path ω)‖ ≤ (∏ i,((m i).factorial:ℝ)⁻¹)*‖B.path ω‖ :=
      integrateSheetPath_norm_le_factorials m _
    _ ≤ (∏ i,((m i).factorial:ℝ)⁻¹)*(ε/(∏ i,((m i).factorial:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hω hF.le
    _ = ε := mul_div_cancel₀ _ hF.ne'

theorem integrated_smallBall_probability_pos {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d→ℕ)
    {ε : ℝ} (hε : 0<ε) :
    0<P.real {ω | ‖integrateSheetPath m (B.path ω)‖≤ε} := by
  have hbase := B.smallBall_probability_pos
    (div_pos hε (integrateSheetPath_factor_pos m))
  exact hbase.trans_le (integrated_smallBall_mass_ge P B m ε)

end BrownianSharp.AlignmentIntegratedNorm
