module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobErasureProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound OriginalHereditaryTypedJobDefinitions
open OriginalRawSyntaxTransport

theorem argumentsErasure {n : Nat} {arity : Fin n → Nat} (binders Gamma : List Ty)
 (sigma : Ty) {types : List Ty} (args : AuxArguments (Fin n) arity (binders ++ sigma::Gamma) types) :
 argumentsCode (substituteArguments args (prefixErasure binders Gamma sigma)) =
 eraseCode sigma binders.length (argumentsCode args) := by
 cases args with
 | nil => rfl
 | cons q rest =>
   simp only [substituteArguments,argumentsCode,eraseCode,
     OriginalRawSyntaxTransportTypedSupportProof.typedErasure,argumentsErasure binders Gamma sigma rest]
termination_by sizeOf args

theorem erasedCore {n : Nat} {arity : Fin n → Nat} (role typ : Nat)
 (binders Gamma : List Ty) (sigma : Ty) (code : Code (Fin n))
 (h : CoreTyped arity role typ (binders ++ sigma::Gamma) code) :
 CoreTyped arity role typ (binders ++ Gamma) (eraseCode sigma binders.length code) := by
 cases h with
 | term q =>
   rw [← OriginalRawSyntaxTransportTypedSupportProof.typedErasure binders Gamma sigma _ q]
   exact CoreTyped.term _
 | arguments args =>
   rw [← argumentsErasure binders Gamma sigma args]
   exact CoreTyped.arguments _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobErasureProof
