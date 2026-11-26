module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem countValues (head acc left right lc rc : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right head))) :
    Nonempty (Derivation body Delta (programGraph leftCount lc ![head,acc,left,right])) ∧
    Nonempty (Derivation body Delta (programGraph rightCount rc ![head,acc,left,right])) :=
  ⟨binaryValue ArgumentEntryCount.count (.projection 2) (.projection 0) lc left head ![head,acc,left,right]
      hl (projectionValue 2 ![head,acc,left,right]) (projectionValue 0 ![head,acc,left,right]),
   binaryValue ArgumentEntryCount.count (.projection 3) (.projection 0) rc right head ![head,acc,left,right]
      hr (projectionValue 3 ![head,acc,left,right]) (projectionValue 0 ![head,acc,left,right])⟩

theorem stepIntro (head left right lc rc : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right head)))
    (he : Nonempty (Derivation body Delta (eqn lc rc))) :
    Nonempty (Derivation body Delta (programGraph step (numeral 1) ![head,numeral 1,left,right])) := by
  let xs : Fin 4 → OTerm alpha := ![head,numeral 1,left,right]
  obtain ⟨hl',hr'⟩ := countValues head (numeral 1) left right lc rc hl hr
  have hq := binaryValue InternalEqualityTest.equalityTest leftCount rightCount (numeral 1) lc rc xs
    (InternalEqualityTestCompositionProof.equalityOfEqual lc rc he) hl' hr'
  exact successorBranchIntro (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
    (numeral 1) (numeral 0) xs hq (projectionValue 1 xs)

theorem stepRecover (head acc left right lc rc : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right head)))
    (hs : Nonempty (Derivation body Delta (programGraph step (numeral 1) ![head,acc,left,right]))) :
    Nonempty (Derivation body Delta (eqn lc rc ⊓ eqn acc (numeral 1))) := by
  let P := eqn lc rc
  apply formulaCases P
  · obtain ⟨hl',hr'⟩ := countValues head acc left right lc rc (withHyp hl P) (withHyp hr P)
    have he : Nonempty (Derivation body (P :: Delta) (eqn lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    let xs : Fin 4 → OTerm alpha := ![head,acc,left,right]
    have hq := binaryValue InternalEqualityTest.equalityTest leftCount rightCount (numeral 1) lc rc xs
      (InternalEqualityTestCompositionProof.equalityOfEqual lc rc he) hl' hr'
    have hp := successorBranchElim (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
      (numeral 1) (numeral 0) xs hq (withHyp hs P)
    obtain ⟨ha⟩ := valueUnique (.projection (1 : Fin 4)) acc (numeral 1) xs (projectionValue 1 xs) hp
    obtain ⟨he⟩ := he
    exact ⟨Derivation.conjunctionIntroduction he ha⟩
  · obtain ⟨hl',hr'⟩ := countValues head acc left right lc rc (withHyp hl P.not) (withHyp hr P.not)
    let xs : Fin 4 → OTerm alpha := ![head,acc,left,right]
    have hn : Nonempty (Derivation body (P.not :: Delta) (equal lc rc).not) := by
      simpa only [equalEqn] using (Nonempty.intro (Derivation.hypothesis (body := body)
        (Gamma := P.not :: Delta) List.mem_cons_self) : Nonempty (Derivation body (P.not :: Delta) P.not))
    have hq := sameReject leftCount rightCount lc rc xs hl' hr' hn
    have hz := zeroBranchElim (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
      (numeral 1) xs hq (withHyp hs P.not)
    obtain ⟨he⟩ := valueUnique (constant 4 0) (numeral 1) (numeral 0) xs hz (constantValue 0 xs)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.StepProof
