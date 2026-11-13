module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn)
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax CodedDeletionTraceElimination CodedDeletionTraceTransport
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem entryTransport (entry other left right parameter gamma : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn entry other)))
 (hf : Nonempty (Derivation body Delta (StateFields entry left right parameter gamma))) :
 Nonempty (Derivation body Delta (StateFields other left right parameter gamma)) :=
 andIntro (headTransport leftField left entry other Fin.elim0 he (andLeft hf))
 (andIntro (headTransport rightField right entry other Fin.elim0 he (andLeft (andRight hf)))
 (andIntro (headTransport parameterField parameter entry other Fin.elim0 he (andLeft (andRight (andRight hf))))
 (headTransport gammaField gamma entry other Fin.elim0 he (andRight (andRight (andRight hf))))))
theorem stateTransfer (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace index left right parameter gamma otherLeft otherRight otherParameter otherGamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (StateAt trace index left right parameter gamma)))
 (ht : Nonempty (Derivation body Delta (StateAt trace index otherLeft otherRight otherParameter otherGamma)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W otherLeft otherRight otherParameter)) := by
 apply stateCases trace index left right parameter gamma _ hs
 intro beta j Theta entry hj hf
 have ht' := renameInto ht j Theta hj
 have ha' := renameInto ha j Theta hj
 rw [stateRename] at ht'
 rw [admittedRename] at ha' ⊢
 apply stateCases (trace.relabel j) (index.relabel j) (otherLeft.relabel j) (otherRight.relabel j)
   (otherParameter.relabel j) (otherGamma.relabel j) _ ht'
 intro beta2 k Theta2 other hk hother
 have hlookup := renameInto (andLeft hf) k Theta2 hk
 have hfields := renameInto (andRight hf) k Theta2 hk
 have ha'' := renameInto ha' k Theta2 hk
 rw [graph2Rename] at hlookup
 rw [fieldsRename] at hfields
 rw [admittedRename] at ha'' ⊢
 have he := valueUnique InternalRawListRecursion.lookup (entry.relabel k) other
   (Fin.cons ((index.relabel j).relabel k) (Fin.cons ((trace.relabel j).relabel k) Fin.elim0))
   hlookup (andLeft hother)
 exact fieldsTransfer R H G M W other
   ((left.relabel j).relabel k) ((right.relabel j).relabel k) ((parameter.relabel j).relabel k) ((gamma.relabel j).relabel k)
   ((otherLeft.relabel j).relabel k) ((otherRight.relabel j).relabel k) ((otherParameter.relabel j).relabel k) ((otherGamma.relabel j).relabel k)
   (entryTransport _ _ _ _ _ _ he hfields) (andRight hother) ha''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStateProof
