module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions
/-- Actual native typed reconstruction, including administrative argument-list
jobs. This is not a Program validity test or an assumption about malformed jobs. -/
inductive CoreTyped {n : Nat} (arity : Fin n → Nat) : Nat → Nat → List Ty → Code (Fin n) → Prop where
 | term {Gamma tau} (q : AuxTerm (Fin n) arity Gamma tau) :
     CoreTyped arity 0 (typeNumber tau) Gamma (termCode q)
 | arguments {Gamma types} (args : AuxArguments (Fin n) arity Gamma types) :
     CoreTyped arity 1 0 Gamma (argumentsCode args)
def Typed {n : Nat} (arity : Fin n → Nat) (a : Job n) : Prop :=
 CoreTyped arity a.role a.typ a.core.context a.core.code
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
