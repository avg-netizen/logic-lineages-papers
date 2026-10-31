module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Literal parse-tree nodes. No ordinal evaluation, reassociation or zero
elision is performed. Each of Add, ExpProd and Psi is one binary node. -/
def ordinalLiteralNodes {ι : Type} : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Nat
  | .var _ | .zero | .one | .omega => 1
  | .add f g | .emul f g | .collapse f g =>
      ordinalLiteralNodes f + ordinalLiteralNodes g + 1

/-- The unconditional weighted size in paper05 Appendix A, Proposition
`wwsc:prop:finite`: an ExpProd head has weight two. Unlike partial size,
this does not stop at a whole-free subtree. -/
def ordinalLiteralWeight {ι : Type} : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Nat
  | .var _ | .zero | .one | .omega => 1
  | .add f g | .collapse f g => ordinalLiteralWeight f + ordinalLiteralWeight g + 1
  | .emul f g => 2 * ordinalLiteralWeight f + ordinalLiteralWeight g + 1

end LogicLineages.OrdinalComparison.Source
