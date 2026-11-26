module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineEmptyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationResultStack (emptyState)
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Empty work is selected internally from the original nested pair graph. -/
theorem emptyFixed (mode : Mode)
    (results state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 emptyState state results))) :
    Nonempty (Derivation body Gamma (graph1 (transition mode) state state)) := by
  apply programCases InternalPairing.pairing (Fin.cons z (Fin.cons results Fin.elim0)) _
  intro β j Delta packed hj hp
  simp only [graph1Rename]
  simp only [consTermRename,emptyRename,zRelabel] at hp
  have hs' := renameInto hs j Delta hj
  simp only [graph1Rename] at hs'
  let xs : Fin 1 → OTerm β := Fin.cons (results.relabel j) Fin.elim0
  let ss : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  have hi := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1)
    (.projection 0) packed z (results.relabel j) xs hp
    (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1)
    (pairOf (InternalAcceptance.constantZero 1) (.projection 0))
    (state.relabel j) (suc z) packed xs hs'
    (InternalLessThanSupportProof.oneConstantValue xs) hi
  have hstatus := pairLeft (state.relabel j) (suc z) packed ho
  have hwork := unaryValue InternalUnpair.left InternalUnpair.right z packed ss
    (pairLeft packed z (results.relabel j) hp)
    (pairRight (state.relabel j) (suc z) packed ho)
  have haccept := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  apply successorBranchIntro _ _ _ (state.relabel j) z ss haccept
  exact zeroBranchIntro _ _ _ (state.relabel j) ss hwork (projectionValue 0 ss)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineEmptyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineEmptyProof
