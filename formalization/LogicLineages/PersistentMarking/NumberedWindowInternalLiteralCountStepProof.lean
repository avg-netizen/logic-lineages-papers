module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique equalEqn)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryValue)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc z)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCount

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private theorem countValues (head acc left right lc rc : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (programGraph entryCount lc ![left,head])))
    (hr : Nonempty (Derivation body Delta (programGraph entryCount rc ![right,head]))) :
    Nonempty (Derivation body Delta (programGraph leftCount lc ![head,acc,left,right])) ∧
    Nonempty (Derivation body Delta (programGraph rightCount rc ![head,acc,left,right])) :=
  ⟨binaryValue entryCount (.projection 2) (.projection 0) lc left head ![head,acc,left,right]
      hl (projectionValue 2 ![head,acc,left,right]) (projectionValue 0 ![head,acc,left,right]),
   binaryValue entryCount (.projection 3) (.projection 0) rc right head ![head,acc,left,right]
      hr (projectionValue 3 ![head,acc,left,right]) (projectionValue 0 ![head,acc,left,right])⟩

/-- Same selected physical count step; a true result certifies equal actual
head counts and acceptance of the actual previous accumulator. -/
theorem stepRecover (head acc left right lc rc : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (programGraph entryCount lc ![left,head])))
    (hr : Nonempty (Derivation body Delta (programGraph entryCount rc ![right,head])))
    (hs : Nonempty (Derivation body Delta (programGraph step (suc z) ![head,acc,left,right]))) :
    Nonempty (Derivation body Delta (eqn lc rc ⊓ eqn acc (suc z))) := by
  let P := eqn lc rc
  apply formulaCases P
  · obtain ⟨hl',hr'⟩ := countValues head acc left right lc rc (withHyp hl P) (withHyp hr P)
    have he : Nonempty (Derivation body (P :: Delta) (eqn lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    let xs : Fin 4 → OTerm alpha := ![head,acc,left,right]
    have hq := binaryValue equalityTest leftCount rightCount (suc z) lc rc xs
      (equalityOfEqual lc rc he) hl' hr'
    have hp := successorBranchElim (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
      (suc z) z xs hq (withHyp hs P)
    obtain ⟨ha⟩ := valueUnique (.projection (1 : Fin 4)) acc (suc z) xs (projectionValue 1 xs) hp
    obtain ⟨he⟩ := he
    exact ⟨Derivation.conjunctionIntroduction he ha⟩
  · obtain ⟨hl',hr'⟩ := countValues head acc left right lc rc (withHyp hl P.not) (withHyp hr P.not)
    let xs : Fin 4 → OTerm alpha := ![head,acc,left,right]
    have hn : Nonempty (Derivation body (P.not :: Delta) (equal lc rc).not) := by
      simpa only [equalEqn] using (Nonempty.intro (Derivation.hypothesis (body := body)
        (Gamma := P.not :: Delta) List.mem_cons_self) : Nonempty (Derivation body (P.not :: Delta) P.not))
    have hq := sameReject leftCount rightCount lc rc xs hl' hr' hn
    have hz := zeroBranchElim (sameOf leftCount rightCount) (constant 4 0) (.projection 1)
      (suc z) xs hq (withHyp hs P.not)
    obtain ⟨he⟩ := valueUnique (constant 4 0) (suc z) z xs hz (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

#print axioms stepRecover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountStepProof
