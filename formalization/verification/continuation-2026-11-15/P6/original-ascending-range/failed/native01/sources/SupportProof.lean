module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilImpossible (index : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) z index))) :
    Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
  obtain ⟨he⟩ := valueUnique contains (suc z) z ![z,index] hm (containsNil index)
  exact ⟨sucNeZeroApply he⟩

theorem singletonMember (code head index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) code index))) :
    Nonempty (Derivation body Delta (eqn index head)) := by
  apply formulaCases (eqn head index)
  · exact ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
  · let A := (eqn head index).not
    have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover code head z index (numeral 1)
      (withHyp hc A) (by simpa only [equalEqn] using hn) (withHyp hm A)
    obtain ⟨hf⟩ := nilImpossible index ht
    exact ⟨Derivation.explosion hf⟩

theorem lessNext (index bound : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess index bound))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess index (suc bound))) := by
  obtain ⟨hp⟩ := InternalQuotientComparisonProof.actualRightSuccessorOrder body alpha index bound
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed hp Delta) h⟩

theorem nextSplit (index bound : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess index (suc bound)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess index bound ⊔ eqn index bound)) := by
  obtain ⟨hp⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body alpha index bound
  rw [InternalSourceInversionSupportProof.onEquality] at hp
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed hp Delta) h⟩

theorem singletonValue (bound previous one : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode one bound z))) :
    Nonempty (Derivation body Delta (graph2 singleton one bound previous)) :=
  binaryValue InternalListCodec.consCode (.projection 0) (InternalAcceptance.constantZero 2)
    one bound z ![bound,previous] hc (projectionValue 0 ![bound,previous])
    (InternalAcceptanceConjunctionProof.constantZeroValue ![bound,previous])

theorem stepValue (bound previous one out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode one bound z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out previous one))) :
    Nonempty (Derivation body Delta (graph2 step out bound previous)) :=
  binaryValue InternalApplicationValidityStackAppend.append (.projection 1) singleton
    out previous one ![bound,previous] ha (projectionValue 1 ![bound,previous])
    (singletonValue bound previous one hc)

theorem zeroValue : Nonempty (Derivation body Delta (graph1 range z z)) :=
  recursionZeroValue (InternalAcceptance.constantZero 0) step z Fin.elim0
    (InternalAcceptanceConjunctionProof.constantZeroValue Fin.elim0)

theorem successorValue (bound previous one out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 range previous bound)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode one bound z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out previous one))) :
    Nonempty (Derivation body Delta (graph1 range out (suc bound))) := by
  have hs := stepValue bound previous one out hc ha
  unfold graph1 range programGraph at hp ⊢
  unfold graph2 programGraph at hs
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (InternalAcceptance.constantZero 0))
    (OrdinaryArithmetic.graphFormula step) previous bound Fin.elim0)) at hp
  change Nonempty (Derivation body Delta (InternalRecursionGraph.recursion
    (OrdinaryArithmetic.graphFormula (InternalAcceptance.constantZero 0))
    (OrdinaryArithmetic.graphFormula step) out (suc bound) Fin.elim0))
  exact InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction Delta
    (OrdinaryArithmetic.graphFormula (InternalAcceptance.constantZero 0))
    (OrdinaryArithmetic.graphFormula step) out bound previous Fin.elim0 hp hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.SupportProof
