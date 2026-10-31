module
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions
public import LogicLineages.OrdinalComparison.WWScalarTranslationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open ForwardTranslation
/-- Literal exponential-head nesting of an extracted closed positive term. -/
def positiveHeadHeight : ClosedPositive → Nat
  | .one | .omega => 0
  | .add a b => max (positiveHeadHeight a) (positiveHeadHeight b)
  | .emul a b => max (positiveHeadHeight a + 1) (positiveHeadHeight b)
/-- Every direct fixed index in the scalar syntax, including shifts nested in
other shift tails. Repeated occurrences are deliberately preserved. -/
def scalarHeads {ι : Type} : Scalar ι → List ClosedPositive
  | .one | .var _ => []
  | .add a b => scalarHeads a ++ scalarHeads b
  | .shift c a => c :: scalarHeads a
end LogicLineages.OrdinalComparison.Source.SourceClasses
