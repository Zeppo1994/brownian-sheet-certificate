import BrownianSharp.GaussianProjection

/-! Explicit invariance under the unique finite enumeration of an index type. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFintypeIrrelevance

theorem univ_eq {I : Type*} (a b : Fintype I) :
    @Finset.univ I a = @Finset.univ I b := by
  have hab : a=b := Subsingleton.elim _ _
  cases hab
  rfl

theorem sum_univ_eq {I V : Type*} [AddCommMonoid V]
    (a b : Fintype I) (f : I → V) :
    (@Finset.univ I a).sum f = (@Finset.univ I b).sum f := by
  rw [univ_eq a b]

theorem card_eq {I : Type*} (a b : Fintype I) :
    @Fintype.card I a = @Fintype.card I b := by
  have hab : a=b := Subsingleton.elim _ _
  cases hab
  rfl

theorem projection_fintype_eq {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : Fintype I) (e : I → H) (v : H) :
    @GaussianProjection.projection H I _ _ a (Classical.decEq I) e v =
      @GaussianProjection.projection H I _ _ b (Classical.decEq I) e v := by
  change (@Finset.univ I a).sum (fun i => ⟪e i,v⟫ • e i) =
    (@Finset.univ I b).sum (fun i => ⟪e i,v⟫ • e i)
  exact sum_univ_eq a b _

end BrownianSharp.AlignmentFintypeIrrelevance
