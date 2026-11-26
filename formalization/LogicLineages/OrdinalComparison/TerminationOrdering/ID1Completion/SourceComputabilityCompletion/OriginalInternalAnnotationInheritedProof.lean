module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualInherited : OriginalInternalAnnotationInheritedTargets.ActualInherited := by
 intro body alpha Delta index role typ raw arity annotation ha hn hp
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have ha' : Nonempty (Derivation body Delta
  (graph4 (OriginalRawSyntaxTransport.arityOf (.projection 3)) arity index role typ raw)) := by
  -- arityOf depends only on the supplied raw argument.
  exact OriginalRawSyntaxTransportInternalConstructorSubstitutionProof.arityValueAt (.projection 3) arity raw xs (projectionValue 3 xs) ha
 have hlt := binaryValue InternalLessThan.ltTest (.projection 0) (OriginalRawSyntaxTransport.arityOf (.projection 3))
  z index arity xs (InternalLessThanSupportProof.rejectOfNotLess index arity hn) (projectionValue 0 xs) ha'
 have hv := binaryValue InternalPairing.pairing (.projection 1) (.projection 2) annotation role typ xs hp
  (projectionValue 1 xs) (projectionValue 2 xs)
 exact InternalAcceptanceBranchProof.zeroBranchIntro _ OriginalHereditaryAnnotatedExpansion.inherited
  OriginalHereditaryAnnotatedExpansion.childAnnotation annotation xs hlt hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedProof
