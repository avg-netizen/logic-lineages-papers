module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceElimination
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn emb eqnRelabel)
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalRecursionGraphStepSyntaxProof
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax CodedDeletionTraceElimination
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem admittedTransfer (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter otherLeft otherRight otherParameter : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (eqn left otherLeft)))
 (hr : Nonempty (Derivation body Delta (eqn right otherRight)))
 (hp : Nonempty (Derivation body Delta (eqn parameter otherParameter)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W otherLeft otherRight otherParameter)) := by
 let phi : Formula (Fin 3) := AdmittedPair R H G M W (.var 0) (.var 1) (.var 2)
 let ts : Fin 3 → OTerm alpha := ![left,right,parameter]
 let us : Fin 3 → OTerm alpha := ![otherLeft,otherRight,otherParameter]
 have hstart : Nonempty (Derivation body Delta (phi.subst (fun i => emb (ts i)))) := by
   simpa only [phi,admittedSubst,Term.subst,ts,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using ha
 have heq : ∀ i, Nonempty (Derivation body Delta ((emb (ts i)).equal (emb (us i)))) := by
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
   · exact hl
   · exact hr
   · exact hp
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 3 Delta phi
   (fun i => emb (ts i)) (fun i => emb (us i)) heq hstart
 simpa only [phi,admittedSubst,Term.subst,us,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

theorem fieldsTransfer (R : Program 2) (H G : Program 1) (M W : Program 2)
 (entry left right parameter gamma otherLeft otherRight otherParameter otherGamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (StateFields entry left right parameter gamma)))
 (ht : Nonempty (Derivation body Delta (StateFields entry otherLeft otherRight otherParameter otherGamma)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W otherLeft otherRight otherParameter)) :=
 admittedTransfer R H G M W left right parameter otherLeft otherRight otherParameter
   (valueUnique leftField left otherLeft (Fin.cons entry Fin.elim0) (andLeft hs) (andLeft ht))
   (valueUnique rightField right otherRight (Fin.cons entry Fin.elim0) (andLeft (andRight hs)) (andLeft (andRight ht)))
   (valueUnique parameterField parameter otherParameter (Fin.cons entry Fin.elim0)
     (andLeft (andRight (andRight hs))) (andLeft (andRight (andRight ht)))) ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTransport
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTransport
