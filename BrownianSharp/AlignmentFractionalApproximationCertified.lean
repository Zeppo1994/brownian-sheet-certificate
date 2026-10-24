import BrownianSharp.AlignmentFractionalHigherOrderConditional

/-! Public unconditional all-smoothness fractional approximation and width
ratio claim. The actual even-order lower theorem is already instantiated in
the imported certified proof. -/

namespace BrownianSharp.AlignmentFractionalApproximationCertified

abbrev FullFractionalApproximationStatement :=
  BrownianSharp.AlignmentFractionalHigherOrderConditional.FractionalHigherOrderStatement

theorem fractionalApproximation_certified : FullFractionalApproximationStatement :=
  BrownianSharp.AlignmentFractionalHigherOrderConditional.fractional_higher_order_certified

end BrownianSharp.AlignmentFractionalApproximationCertified
