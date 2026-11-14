module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.RankedProof
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
theorem ranked : Targets.InternalRanked := by
  intro n arity body alpha Delta raw symbol symbols types hp
  have hd := OriginalHeadWindow.InternalProof.internalBranch n arity body alpha Delta (5 : Fin 6) raw symbol symbols types (numeral 1) hp
  let xs : Fin 3 → OTerm alpha := Fin.cons symbol (Fin.cons symbols (Fin.cons types Fin.elim0))
  have hr := resultValue 5 symbol symbols types (numeral 0)
    (constantValue (body := body) (Delta := Delta) 0 (Fin.cons symbol Fin.elim0))
  have fr := typeFactor _ symbol symbols types (numeral 0) hr
  have hz : Nonempty (Derivation body Delta (graph3 (constant 3 0) (numeral 0) symbol symbols types)) := constantValue 0 xs
  have fg := typeFactor _ symbol symbols types (numeral 0) hz
  have fs : Nonempty (Derivation body Delta (graph3
      (.composition contains ![.projection 1,.projection 0]) (numeral 1) symbol symbols types)) ↔
      Nonempty (Derivation body Delta (member symbols symbol)) :=
    ⟨fun h => binaryRecover contains (.projection 1) (.projection 0) (numeral 1) symbols symbol xs h
      (projectionValue 1 xs) (projectionValue 0 xs),
     fun h => binaryValue contains (.projection 1) (.projection 0) (numeral 1) symbols symbol xs h
      (projectionValue 1 xs) (projectionValue 0 xs)⟩
  constructor
  · intro h
    have hc := conjunctionRecover _ _ xs (hd.mp h)
    have ht := conjunctionRecover _ _ xs (andRight hc)
    exact andIntro (fs.mp (andLeft hc)) (fr.mp (andLeft ht))
  · intro h
    have hg := andRight h
    have hargs : Nonempty (Derivation body Delta (graph3 (rankedArguments n arity) (numeral 1) symbol symbols types)) :=
      branchBoth (arityAt n arity) (constant 3 1) (typeMember (constant 3 0)) (numeral 1) xs
        (constantValue 1 xs) (fg.mpr hg)
    exact hd.mpr (conjunctionAccept _ _ xs (fs.mpr (andLeft h))
      (conjunctionAccept _ _ xs (fr.mpr hg) hargs))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.RankedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.RankedProof
