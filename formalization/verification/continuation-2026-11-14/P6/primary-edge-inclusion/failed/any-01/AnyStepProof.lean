module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalAcceptanceNormalizationProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open PrimaryExpansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem stepHit (E : Program 3) (head rest candidate parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 E (suc z) head candidate parameter))) :
    Nonempty (Derivation body Delta (graph4 (anyStep E) (suc z) head rest candidate parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,candidate,parameter]
  let query : Program 4 := .composition E ![.projection 0,.projection 2,.projection 3]
  have hq : Nonempty (Derivation body Delta (programGraph query (suc z) xs)) := by
    apply compositionValue E ![.projection 0,.projection 2,.projection 3]
      (suc z) xs ![head,candidate,parameter] he
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs)
      (Fin.cases (projectionValue 3 xs) (fun j => Fin.elim0 j))) i
  exact successorBranchIntro (normalize query) (.projection 1) (InternalLessThan.constantOne 4)
    (suc z) z xs (normalizeAccept query xs hq) (InternalLessThanSupportProof.oneConstantValue xs)

theorem stepTail (E : Program 3) (head candidate parameter : OTerm alpha) :
    Nonempty (Derivation body Delta (graph4 (anyStep E) (suc z) head (suc z) candidate parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![head,suc z,candidate,parameter]
  let query : Program 4 := .composition E ![.projection 0,.projection 2,.projection 3]
  let A := programGraph query (suc z) xs
  apply formulaCases A
  · exact successorBranchIntro (normalize query) (.projection 1) (InternalLessThan.constantOne 4)
      (suc z) z xs (normalizeAccept query xs ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (InternalLessThanSupportProof.oneConstantValue xs)
  · exact zeroBranchIntro (normalize query) (.projection 1) (InternalLessThan.constantOne 4)
      (suc z) xs (normalizeReject query xs ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (projectionValue 1 xs)

theorem consHit (E : Program 3) (raw head tail candidate parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (he : Nonempty (Derivation body Delta (graph3 E (suc z) head candidate parameter))) :
    Nonempty (Derivation body Delta (graph3 (anyEdge E) (suc z) raw candidate parameter)) := by
  apply programCases (anyEdge E) (Fin.cons tail (Fin.cons candidate (Fin.cons parameter Fin.elim0))) _
  intro beta j Theta rest hj hr
  simp only [graph3Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have he' := renameInto he j Theta hj
  simp only [graph3Rename,sucRelabel,zRelabel] at he'
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 2) (anyStep E)
    (raw.relabel j) (head.relabel j) (tail.relabel j) rest (suc z)
    ![candidate.relabel j,parameter.relabel j] hc' hr
    (stepHit E (head.relabel j) rest (candidate.relabel j) (parameter.relabel j) he')

theorem consTail (E : Program 3) (raw head tail candidate parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (anyEdge E) (suc z) tail candidate parameter))) :
    Nonempty (Derivation body Delta (graph3 (anyEdge E) (suc z) raw candidate parameter)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 2) (anyStep E)
    raw head tail (suc z) (suc z) ![candidate,parameter] hc hr (stepTail E head candidate parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyStepProof
