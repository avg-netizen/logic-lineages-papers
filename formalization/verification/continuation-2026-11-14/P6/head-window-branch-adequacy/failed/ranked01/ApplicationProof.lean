module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.ApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalHeadWindow
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SupportProof
theorem application : Targets.InternalApplication := by
  intro n arity body alpha Delta raw payload sigma tau symbols types hp hpair
  have hd := OriginalHeadWindow.InternalProof.internalBranch n arity body alpha Delta (4 : Fin 6) raw payload symbols types (numeral 1) hp
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha payload sigma tau) hpair
  let xs : Fin 3 → OTerm alpha := Fin.cons payload (Fin.cons symbols (Fin.cons types Fin.elim0))
  have hr : Nonempty (Derivation body Delta (graph3
      (.composition (OriginalHeadResult.branchResult 4) (fun _ : Fin 1 => .projection 0)) tau payload symbols types)) :=
    resultValue 4 payload symbols types tau ⟨Derivation.conjunctionRight hi⟩
  have hl : Nonempty (Derivation body Delta (graph3 (leftOf (.projection 0)) sigma payload symbols types)) :=
    unaryValue InternalUnpair.left (.projection 0) sigma payload xs ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 xs)
  have ha : Nonempty (Derivation body Delta (graph3 (succOf (.projection 0)) (suc payload) payload symbols types)) :=
    unaryValue .succ (.projection 0) (suc payload) payload xs
      (successorValue (Fin.cons payload Fin.elim0)) (projectionValue 0 xs)
  have fr := typeFactor _ payload symbols types tau hr
  have fl := typeFactor _ payload symbols types sigma hl
  have fa := typeFactor _ payload symbols types (suc payload) ha
  constructor
  · intro h
    have hc := conjunctionRecover _ _ xs (hd.mp h)
    have hargs := conjunctionRecover _ _ xs (andRight hc)
    exact andIntro (fr.mp (andLeft hc)) (andIntro (fa.mp (andLeft hargs)) (fl.mp (andRight hargs)))
  · intro h
    exact hd.mpr (conjunctionAccept _ _ xs (fr.mpr (andLeft h))
      (conjunctionAccept _ _ xs (fa.mpr (andLeft (andRight h))) (fl.mpr (andRight (andRight h)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.ApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.ApplicationProof
