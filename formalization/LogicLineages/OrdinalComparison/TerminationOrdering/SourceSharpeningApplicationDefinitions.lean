module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningCompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationPostProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplication
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding SourceSharpening

/-- Standard literal Option lifting of the actual syntax relation. Both
undefined applications must really be none; defined outputs must be Sharp. -/
def OutputSharp {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    Option (MarkedTerm Symbol arity Gamma tau) → Option (MarkedTerm Symbol arity Gamma tau) → Prop
  | none,none => True
  | some q,some u => Sharp Symbol arity Gamma q u
  | _,_ => False

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplication
