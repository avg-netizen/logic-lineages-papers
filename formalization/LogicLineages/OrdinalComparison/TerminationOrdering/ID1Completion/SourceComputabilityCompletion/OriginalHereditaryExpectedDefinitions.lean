module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditarySettledObserverDefinitions
/-- Pure native projection, not a runtime decoder or validity assertion. -/
def argumentTypes {n : Nat} : Code (Fin n) → List Ty
 | .argumentsCons tau _ rest => tau :: argumentTypes rest
 | _ => []
def argumentValues (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) : List Nat :=
 (argumentList args).map (fun q => Nat.pair (typeNumber q.1) (settledValue R c ⟨Gamma,q⟩))
/-- One common semantic depth for a finite argument row; administrative cons
nodes do not decrement this depth. -/
def argumentDepth {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) : Nat :=
 ((argumentList args).map (fun q => OriginalHereditaryNativeBoundDefinitions.weight ⟨Gamma,q⟩)).sum
/-- Native relational specification, never used in a Program definition. -/
def Expected {n : Nat} (arity : Fin n → Nat) (R : Program 2) (c : Nat) (a : Job n) (v : Nat) : Prop :=
 (∃ q : Packed (Fin n) arity a.core.context,
   a.role = 0 ∧ a.typ = typeNumber q.1 ∧ a.core.code = termCode q.2 ∧
   v = settledValue R c ⟨a.core.context,q⟩) ∨
 (∃ types, ∃ (args : AuxArguments (Fin n) arity a.core.context types),
   a.role = 1 ∧ a.typ = 0 ∧ a.core.code = argumentsCode args ∧
   v = numbersNumber (argumentValues R c args))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedDefinitions
