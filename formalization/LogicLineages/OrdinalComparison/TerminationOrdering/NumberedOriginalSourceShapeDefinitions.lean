module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof

@[expose] public section
/-! Actual original-only structural mask. Typed decoding remains responsible
for index, arity and type validity: this mask alone is NOT an untyped parser.
Auxiliary application, bottom and finite-numbered heads are excluded; original
functional application is still the ordinary application HEAD.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShape
open NumberedAuxiliaryCoding

def codeShape {Symbol : Type} : Code Symbol → Bool
  | .var _ | .argumentsNil => true
  | .lam _ body | .ordinary _ body => codeShape body
  | .argumentsCons _ q rest => codeShape q && codeShape rest
  | .app _ _ _ | .bottom _ | .numbered _ _ _ _ _ _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShape
