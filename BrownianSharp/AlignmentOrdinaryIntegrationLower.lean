import BrownianSharp.AlignmentFractionalDensity
import BrownianSharp.AlignmentOperatorKernelTrace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentOrdinaryIntegrationLower

open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalTranslation

theorem profileToL2_inner (f g : C(UnitInterval, ℝ)) :
    ⟪profileToL2 f, profileToL2 g⟫_ℝ =
      ∫ x in Set.Icc (0:ℝ) 1,
        f (clipUnit x) * g (clipUnit x) ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [profileToL2_coe f, profileToL2_coe g,
    ae_restrict_mem measurableSet_Icc] with x hf hg hx
  have hclip : clipUnit x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simp [clipUnit, hx.1, hx.2]
  rw [hf, hg, hclip]
  simp
  ring

theorem clippedProfileIntegral_eq_interval (f g : C(UnitInterval, ℝ)) :
    (∫ x in Set.Icc (0:ℝ) 1, f (clipUnit x) * g (clipUnit x) ∂volume) =
      ∫ t in (0:ℝ)..1, f (clipUnit t) * g (clipUnit t) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

def unitSourceProbability : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)

instance : IsProbabilityMeasure unitSourceProbability where
  measure_univ := by
    rw [unitSourceProbability, Measure.restrict_apply_univ]
    simp [Real.volume_Icc]

def unitTargetMeasure : Measure UnitInterval :=
  Measure.map clipUnit unitSourceProbability

instance : IsProbabilityMeasure unitTargetMeasure := by
  dsimp [unitTargetMeasure]
  infer_instance

theorem integral_unitTargetMeasure (f : C(UnitInterval, ℝ)) :
    ∫ t, (f t)^2 ∂unitTargetMeasure = ‖profileToL2 f‖^2 := by
  rw [unitTargetMeasure, integral_map clipUnit_continuous.aemeasurable]
  · rw [unitSourceProbability]
    change (∫ x in Set.Icc (0:ℝ) 1, f (clipUnit x)^2 ∂volume) = _
    calc
      (∫ x in Set.Icc (0:ℝ) 1, f (clipUnit x)^2 ∂volume) =
          ∫ x in Set.Icc (0:ℝ) 1, f (clipUnit x) * f (clipUnit x) ∂volume := by
        congr 1
        ext x
        ring
      _ = ⟪profileToL2 f, profileToL2 f⟫_ℝ := (profileToL2_inner f f).symm
      _ = ‖profileToL2 f‖^2 := real_inner_self_eq_norm_sq _
  · exact (f.continuous.pow 2).aestronglyMeasurable

def halfFrequency (m : ℕ) : ℝ := ((m:ℝ) + 1/2) * Real.pi

def cosineProfile (m : ℕ) : C(UnitInterval, ℝ) where
  toFun t := Real.sqrt 2 * Real.cos (halfFrequency m * t.1)
  continuous_toFun := by fun_prop

def sineProfile (m : ℕ) : C(UnitInterval, ℝ) where
  toFun t := Real.sqrt 2 * Real.sin (halfFrequency m * t.1)
  continuous_toFun := by fun_prop

def cosineSource (m : ℕ) : UnitL2 := profileToL2 (cosineProfile m)

def sineProfileL2 (m : ℕ) : Lp ℝ 2 (volume.restrict UnitInterval) :=
  BoundedContinuousFunction.toLp 2 (volume.restrict UnitInterval) ℝ
    ((extendUnitProfile (sineProfile m)))

theorem integral_cos_integer_pi (z : ℤ) :
    (∫ t in (0:ℝ)..1, Real.cos (Real.pi * (z:ℝ) * t)) =
      if z = 0 then 1 else 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · have hc : Real.pi * (z:ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hz)
    have hcomp := intervalIntegral.integral_comp_mul_left (f:=Real.cos)
      (a:=(0:ℝ)) (b:=1) (c:=Real.pi * (z:ℝ)) hc
    rw [show (fun t : ℝ => Real.cos (Real.pi * (z:ℝ) * t)) =
      fun t => Real.cos ((Real.pi * (z:ℝ)) * t) by rfl]
    rw [hcomp, integral_cos]
    have hsin : Real.sin (Real.pi * (z:ℝ)) = 0 := by
      simpa [mul_comm] using Real.sin_int_mul_pi z
    simp [hz, hsin]

theorem integral_halfFrequency_cos_mul_cos (m n : ℕ) :
    (∫ t in (0:ℝ)..1,
      Real.cos (halfFrequency m * t) * Real.cos (halfFrequency n * t)) =
        if m = n then (1/2:ℝ) else 0 := by
  rw [show (fun t : ℝ => Real.cos (halfFrequency m * t) *
      Real.cos (halfFrequency n * t)) = fun t =>
        (Real.cos (halfFrequency m * t) * Real.cos (halfFrequency n * t)) by rfl]
  have hprod (t : ℝ) :
      Real.cos (halfFrequency m * t) * Real.cos (halfFrequency n * t) =
        (Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t) +
          Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t))/2 := by
    have hsub : halfFrequency m*t-halfFrequency n*t =
        ((m:ℝ)-(n:ℝ))*Real.pi*t := by dsimp [halfFrequency]; ring
    have hadd : halfFrequency m*t+halfFrequency n*t =
        ((m:ℝ)+(n:ℝ)+1)*Real.pi*t := by dsimp [halfFrequency]; ring
    calc
      _ = (Real.cos (halfFrequency m*t-halfFrequency n*t) +
          Real.cos (halfFrequency m*t+halfFrequency n*t))/2 := by
        rw [← Real.two_mul_cos_mul_cos]
        ring
      _ = _ := by rw [hsub, hadd]
  have hInt (z : ℤ) : (∫ t in (0:ℝ)..1, Real.cos (Real.pi*(z:ℝ)*t)) =
      if z=0 then 1 else 0 := integral_cos_integer_pi z
  rw [intervalIntegral.integral_congr (fun t _ => hprod t), intervalIntegral.integral_div]
  have hc1 : Continuous (fun t : ℝ => Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ => Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) := by fun_prop
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1)]
  have hfirst : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) =
        if ((m:Int)-(n:Int):ℤ)=0 then 1 else 0 := by
    have harg (t : ℝ) : Real.pi * (((m:Int)-(n:Int):ℤ):ℝ) * t =
        ((m:ℝ)-(n:ℝ))*Real.pi*t := by push_cast; ring
    have hfun : (fun t : ℝ => Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) =
        fun t => Real.cos (Real.pi * (((m:Int)-(n:Int):ℤ):ℝ) * t) :=
      funext fun t => congrArg Real.cos (harg t).symm
    rw [hfun]
    exact hInt ((m:Int)-(n:Int))
  have hsecond : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) =
        if ((m:Int)+(n:Int)+1:ℤ)=0 then 1 else 0 := by
    have harg (t : ℝ) : Real.pi * (((m:Int)+(n:Int)+1:ℤ):ℝ) * t =
        ((m:ℝ)+(n:ℝ)+1)*Real.pi*t := by push_cast; ring
    have hfun : (fun t : ℝ => Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) =
        fun t => Real.cos (Real.pi * (((m:Int)+(n:Int)+1:ℤ):ℝ) * t) :=
      funext fun t => congrArg Real.cos (harg t).symm
    rw [hfun]
    exact hInt ((m:Int)+(n:Int)+1)
  have hfirst' : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) = if m=n then 1 else 0 := by
    rw [hfirst]
    have hi : ((m:Int)-(n:Int):ℤ)=0 ↔ m=n := by omega
    simp [hi]
  have hsecond' : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) = 0 := by
    rw [hsecond]
    have hne : ((m:Int)+(n:Int)+1:ℤ) ≠ 0 := by omega
    simp [hne]
  rw [hfirst', hsecond']
  by_cases hmn : m=n <;> simp [hmn]

theorem integral_halfFrequency_sin_mul_sin (m n : ℕ) :
    (∫ t in (0:ℝ)..1,
      Real.sin (halfFrequency m * t) * Real.sin (halfFrequency n * t)) =
        if m = n then (1/2:ℝ) else 0 := by
  have hprod (t : ℝ) :
      Real.sin (halfFrequency m * t) * Real.sin (halfFrequency n * t) =
        (Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t) -
          Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t))/2 := by
    have hsub : halfFrequency m*t-halfFrequency n*t =
        ((m:ℝ)-(n:ℝ))*Real.pi*t := by dsimp [halfFrequency]; ring
    have hadd : halfFrequency m*t+halfFrequency n*t =
        ((m:ℝ)+(n:ℝ)+1)*Real.pi*t := by dsimp [halfFrequency]; ring
    have hid (x y : ℝ) : 2*Real.sin x*Real.sin y = Real.cos (x-y)-Real.cos (x+y) := by
      rw [Real.cos_sub, Real.cos_add]
      ring
    calc
      _ = (Real.cos (halfFrequency m*t-halfFrequency n*t) -
          Real.cos (halfFrequency m*t+halfFrequency n*t))/2 := by
        rw [← hid]
        ring
      _ = _ := by rw [hsub, hadd]
  have hInt (z : ℤ) : (∫ t in (0:ℝ)..1, Real.cos (Real.pi*(z:ℝ)*t)) =
      if z=0 then 1 else 0 := integral_cos_integer_pi z
  have hc1 : Continuous (fun t : ℝ => Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ => Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) := by fun_prop
  rw [intervalIntegral.integral_congr (fun t _ => hprod t), intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1)]
  have hfirst : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) = if m=n then 1 else 0 := by
    have h0 := integral_halfFrequency_cos_mul_cos m n
    -- The integer-frequency antiderivative gives this scalar identity directly.
    have hInt' : (∫ t in (0:ℝ)..1,
        Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) =
          if m=n then 1 else 0 := by
      rw [show (fun t : ℝ => Real.cos (((m:ℝ)-(n:ℝ))*Real.pi*t)) =
        fun t => Real.cos (Real.pi * (((m:Int)-(n:Int):ℤ):ℝ) * t) by
          funext t; congr 1; push_cast; ring]
      rw [integral_cos_integer_pi]
      have hz : ((m:Int)-(n:Int):ℤ)=0 ↔ m=n := by omega
      simp [hz]
    exact hInt'
  have hsecond : (∫ t in (0:ℝ)..1,
      Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) = 0 := by
    rw [show (fun t : ℝ => Real.cos (((m:ℝ)+(n:ℝ)+1)*Real.pi*t)) =
      fun t => Real.cos (Real.pi * (((m:Int)+(n:Int)+1:ℤ):ℝ) * t) by
        funext t; congr 1; push_cast; ring]
    rw [integral_cos_integer_pi]
    have hz : ((m:Int)+(n:Int)+1:ℤ) ≠ 0 := by omega
    simp [hz]
  rw [hfirst, hsecond]
  by_cases hmn : m=n <;> simp [hmn]

theorem cosineSource_orthonormal : Orthonormal ℝ cosineSource := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [cosineSource, cosineSource, profileToL2_inner,
    clippedProfileIntegral_eq_interval]
  simp only [cosineProfile, ContinuousMap.coe_mk]
  have hclip : ∀ t ∈ Set.uIcc (0:ℝ) 1, (clipUnit t).1 = t := by
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    have ht1 : t ≤ 1 := by simpa using ht.2
    simp [clipUnit, ht0, ht1]
  rw [intervalIntegral.integral_congr (fun t ht => by
    change (Real.sqrt 2 * Real.cos (halfFrequency m * (clipUnit t).1)) *
      (Real.sqrt 2 * Real.cos (halfFrequency n * (clipUnit t).1)) = _
    rw [hclip t ht])]
  rw [show (∫ t in (0:ℝ)..1,
      (Real.sqrt 2 * Real.cos (halfFrequency m * t)) *
        (Real.sqrt 2 * Real.cos (halfFrequency n * t))) =
      2 * (∫ t in (0:ℝ)..1,
        Real.cos (halfFrequency m * t) * Real.cos (halfFrequency n * t)) by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      calc
        _ = (Real.sqrt 2 * Real.sqrt 2) *
            (Real.cos (halfFrequency m * t) * Real.cos (halfFrequency n * t)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]]
  rw [integral_halfFrequency_cos_mul_cos]
  by_cases h : m=n <;> simp [h]

theorem sineSource_orthonormal :
    Orthonormal ℝ (fun m => profileToL2 (sineProfile m)) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [profileToL2_inner, clippedProfileIntegral_eq_interval]
  simp only [sineProfile, ContinuousMap.coe_mk]
  have hclip : ∀ t ∈ Set.uIcc (0:ℝ) 1, (clipUnit t).1 = t := by
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    have ht1 : t ≤ 1 := by simpa using ht.2
    simp [clipUnit, ht0, ht1]
  rw [intervalIntegral.integral_congr (fun t ht => by
    change (Real.sqrt 2 * Real.sin (halfFrequency m * (clipUnit t).1)) *
      (Real.sqrt 2 * Real.sin (halfFrequency n * (clipUnit t).1)) = _
    rw [hclip t ht])]
  rw [show (∫ t in (0:ℝ)..1,
      (Real.sqrt 2 * Real.sin (halfFrequency m * t)) *
        (Real.sqrt 2 * Real.sin (halfFrequency n * t))) =
      2 * (∫ t in (0:ℝ)..1,
        Real.sin (halfFrequency m * t) * Real.sin (halfFrequency n * t)) by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      calc
        _ = (Real.sqrt 2 * Real.sqrt 2) *
            (Real.sin (halfFrequency m * t) * Real.sin (halfFrequency n * t)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]]
  rw [integral_halfFrequency_sin_mul_sin]
  by_cases h : m=n <;> simp [h]

theorem fractionalOnC_one_cosine (m : ℕ) :
    fractionalOnC 1 (by norm_num) (cosineProfile m) =
      (halfFrequency m)⁻¹ • sineProfile m := by
  ext t
  have hw : 0 < halfFrequency m := by
    dsimp [halfFrequency]
    positivity
  have ht : t.1 ∈ Set.Icc (0:ℝ) 1 := t.2
  rw [fractionalOnC, ContinuousLinearMap.comp_apply]
  rw [fractionalRL_profile 1 (by norm_num) (cosineProfile m)
    t.1 ht.1 ht.2]
  rw [rlIntegral_one_eq_interval]
  change (∫ u in (0:ℝ)..t.1,
      Real.sqrt 2 * Real.cos (halfFrequency m * (clipUnit u).1)) = _
  have hclip : ∀ u ∈ Set.uIcc (0:ℝ) t.1, (clipUnit u).1 = u := by
    intro u hu
    have hu0 : 0 ≤ u := by
      simpa [Set.uIcc, min_eq_left ht.1, max_eq_right ht.1] using hu.1
    have hut : u ≤ t.1 := by
      simpa [Set.uIcc, min_eq_left ht.1, max_eq_right ht.1] using hu.2
    have hu1 : u ≤ 1 := le_trans hut ht.2
    have hc : clipUnit u = ⟨u, ⟨hu0, hu1⟩⟩ := by
      apply Subtype.ext
      simp [clipUnit, hu0, hu1]
    exact congrArg Subtype.val hc
  rw [intervalIntegral.integral_congr (fun u hu => by rw [hclip u hu])]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := Real.cos) (a := (0:ℝ)) (b := t.1) (c := halfFrequency m) (by linarith)
  have hcos : (∫ u in (0:ℝ)..t.1, Real.cos (halfFrequency m * u)) =
      (Real.sin (halfFrequency m * t.1) - Real.sin 0) / halfFrequency m := by
    rw [hcomp, integral_cos]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [intervalIntegral.integral_const_mul, hcos]
  have hfreq : halfFrequency m = Real.pi * ((m:ℝ) + 1/2) := by
    dsimp [halfFrequency]
    ring
  rw [hfreq]
  simp only [Real.sin_zero, sub_zero]
  dsimp [sineProfile, ContinuousMap.smul_apply]
  rw [hfreq]
  field_simp

theorem fractionalRL_one_cosine (m : ℕ) :
    fractionalRL 1 (by norm_num) (cosineSource m) =
      (halfFrequency m)⁻¹ • sineProfile m := by
  change fractionalOnC 1 (by norm_num) (cosineProfile m) = _
  exact fractionalOnC_one_cosine m

theorem fractionalRL_one_cosine_L2_norm (m : ℕ) :
    ‖profileToL2 (fractionalRL 1 (by norm_num) (cosineSource m))‖ =
      (halfFrequency m)⁻¹ := by
  rw [fractionalRL_one_cosine]
  rw [map_smul]
  rw [norm_smul, sineSource_orthonormal.norm_eq_one m]
  have hp : 0 < halfFrequency m := by dsimp [halfFrequency]; positivity
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  simp

def cosineSubspace (D : ℕ) : Submodule ℝ UnitL2 :=
  Submodule.span ℝ (Set.range (fun i : Fin D => cosineSource i))

def cosineFamily (D : ℕ) : Fin D → UnitL2 := fun i => cosineSource i.val

def sineFamily (D : ℕ) : Fin D → UnitL2 := fun i => profileToL2 (sineProfile i.val)

def cosineSubfamily (D : ℕ) :
    (↥(Finset.univ : Finset (Fin D))) → UnitL2 := fun i => cosineFamily D i.1

def sineSubfamily (D : ℕ) :
    (↥(Finset.univ : Finset (Fin D))) → UnitL2 := fun i => sineFamily D i.1

theorem cosineFamily_orthonormal (D : ℕ) : Orthonormal ℝ (cosineFamily D) := by
  exact cosineSource_orthonormal.comp (fun i : Fin D => i.val) Fin.val_injective

theorem sineFamily_orthonormal (D : ℕ) : Orthonormal ℝ (sineFamily D) := by
  exact sineSource_orthonormal.comp (fun i : Fin D => i.val) Fin.val_injective

theorem cosineSubfamily_orthonormal (D : ℕ) : Orthonormal ℝ (cosineSubfamily D) := by
  exact (cosineFamily_orthonormal D).comp
    (fun i : ↥(Finset.univ : Finset (Fin D)) => i.1) Subtype.val_injective

theorem sineSubfamily_orthonormal (D : ℕ) : Orthonormal ℝ (sineSubfamily D) := by
  exact (sineFamily_orthonormal D).comp
    (fun i : ↥(Finset.univ : Finset (Fin D)) => i.1) Subtype.val_injective

theorem orthonormal_sum_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (hv : Orthonormal ℝ v) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖^2 = ∑ i, (c i)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  calc
    ⟪∑ i, c i • v i, ∑ i, c i • v i⟫_ℝ =
        ∑ i, c i * ⟪v i, ∑ j, c j • v j⟫_ℝ := by
      simp only [sum_inner, real_inner_smul_left]
    _ = ∑ i, c i * c i := by simp [hv.inner_right_fintype]
    _ = ∑ i, (c i)^2 := by simp [pow_two]

theorem cosineSubspace_finrank (D : ℕ) :
    Module.finrank ℝ (cosineSubspace D) = D := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (Fin D)) ℝ
      (Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2)) :=
    OrthonormalBasis.span (cosineFamily_orthonormal D) Finset.univ
  have hs : cosineSubspace D =
      Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2) := by
    unfold cosineSubspace
    congr 1
    have hr : Set.range (cosineFamily D) =
        Set.range (fun i : Fin D => cosineSource i) := by
      ext x
      constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, rfl⟩
    have himage : (Finset.univ.image (cosineFamily D) : Set UnitL2) =
        Set.range (cosineFamily D) := by
      ext x
      simp
    rw [himage, hr]
  rw [hs]
  rw [Module.finrank_eq_card_basis b.toBasis]
  simp

theorem cosineSubspace_finiteDimensional (D : ℕ) :
    FiniteDimensional ℝ (cosineSubspace D) := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (Fin D)) ℝ
      (Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2)) :=
    OrthonormalBasis.span (cosineFamily_orthonormal D) Finset.univ
  have hs : cosineSubspace D =
      Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2) := by
    unfold cosineSubspace
    congr 1
    have hr : Set.range (cosineFamily D) =
        Set.range (fun i : Fin D => cosineSource i) := by
      ext x
      constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, rfl⟩
    have himage : (Finset.univ.image (cosineFamily D) : Set UnitL2) =
        Set.range (cosineFamily D) := by
      ext x
      simp
    rw [himage, hr]
  rw [hs]
  exact Module.Finite.of_basis b.toBasis

theorem cosineSubspace_L2energy_lower {D : ℕ} (hD : 0 < D)
    (v : cosineSubspace D) (hv : ‖(v : UnitL2)‖ = 1) :
    ((halfFrequency (D-1))⁻¹)^2 ≤
      ‖profileToL2 (fractionalRL 1 (by norm_num) (v : UnitL2))‖^2 := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (Fin D)) ℝ
      (Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2)) :=
    OrthonormalBasis.span (cosineFamily_orthonormal D) Finset.univ
  have hs : cosineSubspace D =
      Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2) := by
    unfold cosineSubspace
    congr 1
    have hr : Set.range (cosineFamily D) =
        Set.range (fun i : Fin D => cosineSource i) := by
      ext x
      constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, rfl⟩
    have himage : (Finset.univ.image (cosineFamily D) : Set UnitL2) =
        Set.range (cosineFamily D) := by
      ext x
      simp
    rw [himage, hr]
  have hv' : (v : UnitL2) ∈
      Submodule.span ℝ (Finset.univ.image (cosineFamily D) : Set UnitL2) := by
    rw [← hs]
    exact v.2
  let c : (↥Finset.univ) → ℝ := b.toBasis.repr ⟨(v : UnitL2), hv'⟩
  have hrepr : (v : UnitL2) = ∑ i : ↥Finset.univ, c i • cosineFamily D i.1 := by
    have hh := congrArg Subtype.val (b.toBasis.sum_repr ⟨(v : UnitL2), hv'⟩)
    simpa [c, b, OrthonormalBasis.span_apply] using hh.symm
  have hsource : ‖(v : UnitL2)‖^2 = ∑ i : ↥Finset.univ, (c i)^2 := by
    rw [hrepr]
    exact orthonormal_sum_norm_sq (cosineSubfamily D)
      (cosineSubfamily_orthonormal D) c
  let out : UnitL2 →L[ℝ] UnitL2 :=
    (profileToL2).comp (fractionalRL 1 (by norm_num))
  have hout : out (v : UnitL2) =
      ∑ i : ↥Finset.univ,
        (c i * (halfFrequency i.1.val)⁻¹) • sineFamily D i.1 := by
    rw [hrepr]
    dsimp [out]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change profileToL2 (fractionalRL 1 (by norm_num) (c i • cosineSource i.1.val)) = _
    rw [map_smul, fractionalRL_one_cosine, map_smul]
    simp [sineFamily, mul_comm, smul_smul]
  have houtnorm : ‖out (v : UnitL2)‖^2 =
    ∑ i : ↥Finset.univ, (c i * (halfFrequency i.1.val)⁻¹)^2 := by
    rw [hout]
    exact orthonormal_sum_norm_sq (sineSubfamily D)
      (sineSubfamily_orthonormal D) (fun i => c i * (halfFrequency i.1.val)⁻¹)
  have hfreq (i : Fin D) : halfFrequency i.val ≤ halfFrequency (D-1) := by
    have hi : i.val ≤ D-1 := by omega
    dsimp [halfFrequency]
    have hc : (i.val : ℝ) ≤ ((D-1 : ℕ) : ℝ) := by exact_mod_cast hi
    have hc' : (i.val : ℝ) + 1/2 ≤ ((D-1 : ℕ) : ℝ) + 1/2 := by linarith
    exact mul_le_mul_of_nonneg_right hc' Real.pi_pos.le
  have hpos : 0 < halfFrequency (D-1) := by
    dsimp [halfFrequency]
    positivity
  have hterm (i : ↥Finset.univ) :
      ((halfFrequency (D-1))⁻¹)^2 * (c i)^2 ≤
        (c i * (halfFrequency i.1.val)⁻¹)^2 := by
    have hpi : 0 < halfFrequency i.1.val := by
      dsimp [halfFrequency]
      positivity
    have hinv : (halfFrequency (D-1))⁻¹ ≤ (halfFrequency i.1.val)⁻¹ :=
      by simpa [one_div] using one_div_le_one_div_of_le hpi (hfreq i.1)
    have hsquares : ((halfFrequency (D-1))⁻¹)^2 ≤
        ((halfFrequency i.1.val)⁻¹)^2 := by
      have ha0 : 0 ≤ (halfFrequency (D-1))⁻¹ := (inv_nonneg.mpr hpos.le)
      have hb0 : 0 ≤ (halfFrequency i.1.val)⁻¹ := (inv_nonneg.mpr hpi.le)
      nlinarith
    calc
      ((halfFrequency (D-1))⁻¹)^2 * (c i)^2 ≤
          ((halfFrequency i.1.val)⁻¹)^2 * (c i)^2 :=
        mul_le_mul_of_nonneg_right hsquares (sq_nonneg (c i))
      _ = (c i * (halfFrequency i.1.val)⁻¹)^2 := by ring
  have hsumlower :
      ((halfFrequency (D-1))⁻¹)^2 * (∑ i : ↥Finset.univ, (c i)^2) ≤
        ∑ i : ↥Finset.univ, (c i * (halfFrequency i.1.val)⁻¹)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hterm i
  have hsourceone : (∑ i : ↥Finset.univ, (c i)^2) = 1 := by
    rw [← hsource]
    rw [hv]
    norm_num
  have hout_eq : out (v : UnitL2) =
      profileToL2 (fractionalRL 1 (by norm_num) (v : UnitL2)) := rfl
  calc
    ((halfFrequency (D-1))⁻¹)^2 =
        ((halfFrequency (D-1))⁻¹)^2 * (∑ i : ↥Finset.univ, (c i)^2) := by rw [hsourceone]; ring
    _ ≤ ∑ i : ↥Finset.univ, (c i * (halfFrequency i.1.val)⁻¹)^2 := hsumlower
    _ = ‖out (v : UnitL2)‖^2 := houtnorm.symm
    _ = ‖profileToL2 (fractionalRL 1 (by norm_num) (v : UnitL2))‖^2 := by rw [hout_eq]

theorem ordinaryIntegration_approximationNumber_lower_of_subspace
    {D k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) :
    ENNReal.ofReal ((halfFrequency (D-1))⁻¹ *
      Real.sqrt ((D-(k-1):ℕ):ℝ)) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        (fractionalRL 1 (by norm_num)) k := by
  let V := cosineSubspace D
  let T := fractionalRL 1 (by norm_num)
  letI : FiniteDimensional ℝ V := cosineSubspace_finiteDimensional D
  have hD : Module.finrank ℝ V = D := cosineSubspace_finrank D
  let σ : ℝ := (halfFrequency (D-1))⁻¹
  have hσ : 0 ≤ σ := by
    dsimp [σ]
    exact inv_nonneg.mpr (le_of_lt (by dsimp [halfFrequency]; positivity))
  have henergy : ∀ v : V, ‖(v : UnitL2)‖ = 1 →
      σ^2 ≤ ∫ x, (T (v : UnitL2) x)^2 ∂unitTargetMeasure := by
    intro v hv
    rw [integral_unitTargetMeasure]
    exact cosineSubspace_L2energy_lower (by omega) v hv
  have h := AlignmentOperatorKernelTrace.approximationNumber_lower_of_subspace_trace
    unitTargetMeasure T V hD hk hkD σ hσ henergy
  simpa [T, V, σ] using h

theorem ordinaryIntegration_approximationNumber_lower
    {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal (Real.sqrt (k:ℝ) / (2 * Real.pi * (k:ℝ))) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        (fractionalRL 1 (by norm_num)) k := by
  have htrace := ordinaryIntegration_approximationNumber_lower_of_subspace
    (D := 2*k) (k := k) hk (by omega)
  have hnat : 2*k-(k-1) = k+1 := by omega
  have hfreq : halfFrequency (2*k-1) ≤ 2 * Real.pi * (k:ℝ) := by
    have hcast : ((2*k-1:ℕ):ℝ) = 2*(k:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]
      norm_num
    dsimp [halfFrequency]
    rw [hcast]
    nlinarith [Real.pi_pos]
  have hpos : 0 < halfFrequency (2*k-1) := by
    dsimp [halfFrequency]
    positivity
  have hinv : (2 * Real.pi * (k:ℝ))⁻¹ ≤ (halfFrequency (2*k-1))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hpos hfreq
  have hsqrt : Real.sqrt (k:ℝ) ≤ Real.sqrt ((k+1:ℕ):ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ k
  have hlower : Real.sqrt (k:ℝ) / (2 * Real.pi * (k:ℝ)) ≤
      (halfFrequency (2*k-1))⁻¹ * Real.sqrt ((k+1:ℕ):ℝ) := by
    have hprod := mul_le_mul hinv hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hkpos : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
    have hden : 2 * Real.pi * (k:ℝ) ≠ 0 := by positivity
    rw [div_eq_mul_inv]
    calc
      Real.sqrt (k:ℝ) * (2 * Real.pi * (k:ℝ))⁻¹ ≤
          (halfFrequency (2*k-1))⁻¹ * Real.sqrt ((k+1:ℕ):ℝ) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      _ = _ := by rw [mul_comm]
  have hENN := ENNReal.ofReal_le_ofReal hlower
  exact hENN.trans (by simpa [hnat] using htrace)


end BrownianSharp.AlignmentOrdinaryIntegrationLower
