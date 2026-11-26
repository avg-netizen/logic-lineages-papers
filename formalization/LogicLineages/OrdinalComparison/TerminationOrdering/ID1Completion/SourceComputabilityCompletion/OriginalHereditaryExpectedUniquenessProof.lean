module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedUniquenessProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedDefinitions OriginalHereditaryExpectedTargets

theorem actualArgumentTypes {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (args : AuxArguments (Fin n) arity Gamma types) : argumentTypes (argumentsCode args) = types := by
 induction types with
 | nil => cases args; rfl
 | cons sigma types ih =>
   cases args with
   | cons q rest => exact congrArg (List.cons sigma) (ih rest)

theorem deterministic : Deterministic := by
 intro n arity R c a v w hv hw
 rcases hv with ⟨q,hqrole,hqtyp,hqcode,hv⟩ | ⟨types,args,harole,hatyp,hacode,hv⟩
 · rcases hw with ⟨r,hrrole,hrtyp,hrcode,hw⟩ | ⟨types,args,harole,hatyp,hacode,hw⟩
   · have ht := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective (hqtyp.symm.trans hrtyp)
     have hc := hqcode.symm.trans hrcode
     have he : q = r := NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity a.core.context
       (Prod.ext ht hc)
     cases he
     exact hv.trans hw.symm
   · omega
 · rcases hw with ⟨q,hqrole,hqtyp,hqcode,hw⟩ | ⟨other,rest,hrrole,hrtyp,hrcode,hw⟩
   · omega
   · have hc := hacode.symm.trans hrcode
     have ht : types = other := (actualArgumentTypes args).symm.trans
       ((congrArg argumentTypes hc).trans (actualArgumentTypes rest))
     cases ht
     have he := NumberedAuxiliaryCodingProof.argumentCodeInjective (Fin n) arity a.core.context types hc
     cases he
     exact hv.trans hw.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedUniquenessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedUniquenessProof
