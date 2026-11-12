module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions
open OriginalHereditaryTypedJobDefinitions
/-- Every actual decorated constructor or context-deletion successor retains
its exact role, type and reconstructible original typed syntax. -/
def ExpansionClosure : Prop := ∀ n (arity : Fin n → Nat) c (a b : Job n),
 Typed arity a → b ∈ jobs c a → Typed arity b
/-- Only the operational shape required for the native return branch. No
correctness statement about computed child values is included. -/
def ReturnShape : Prop := ∀ n (arity : Fin n → Nat) (a : Job n), Typed arity a →
 a.role = 0 ∨ (a.role = 1 ∧ a.typ = 0 ∧
   (OriginalRawSyntaxTransport.tagValue (codeNumber a.core.code) = 6 ∨
    OriginalRawSyntaxTransport.tagValue (codeNumber a.core.code) = 7))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobTargets
