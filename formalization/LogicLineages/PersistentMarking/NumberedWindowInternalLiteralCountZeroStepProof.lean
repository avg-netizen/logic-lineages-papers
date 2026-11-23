module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc z)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (binaryValue unaryValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique equalEqn)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf succOf)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCount (entryStep)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem equalImpossible (head previous needle : OTerm α)
    (eq : Nonempty (Derivation B Γ (eqn head needle)))
    (h : Nonempty (Derivation B Γ (programGraph entryStep z ![head,previous,needle]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let xs : Fin 3 → OTerm α := ![head,previous,needle]
  have a := binaryValue equalityTest (.projection 0) (.projection 2) (suc z) head needle xs
    (equalityOfEqual head needle eq) (projectionValue 0 xs) (projectionValue 2 xs)
  have inc : Nonempty (Derivation B Γ (programGraph (succOf (.projection 1)) (suc previous) xs)) :=
    unaryValue .succ (.projection 1) (suc previous) previous xs
      (successorValue (Fin.cons previous Fin.elim0)) (projectionValue 1 xs)
  have y : Nonempty (Derivation B Γ (programGraph entryStep (suc previous) xs)) :=
    successorBranchIntro (sameOf (.projection 0) (.projection 2)) (.projection 1)
      (succOf (.projection 1)) (suc previous) z xs a inc
  obtain ⟨e⟩ := valueUnique entryStep (suc previous) z xs y h
  exact ⟨sucNeZeroApply e⟩

theorem zeroStep (head previous needle : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph entryStep z ![head,previous,needle]))) :
    Nonempty (Derivation B Γ ((eqn head needle).not ⊓ eqn previous z)) := by
  let E := eqn head needle
  apply formulaCases E
  · have e : Nonempty (Derivation B (E :: Γ) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := equalImpossible head previous needle e (withHyp h E)
    exact ⟨Derivation.explosion bad⟩
  · let xs : Fin 3 → OTerm α := ![head,previous,needle]
    have p : Derivation B (E.not :: Γ) E.not := Derivation.hypothesis List.mem_cons_self
    have p' : Nonempty (Derivation B (E.not :: Γ) (equal head needle).not) := by
      rw [equalEqn]
      exact ⟨p⟩
    have ct := sameReject (.projection 0) (.projection 2) head needle xs
      (projectionValue 0 xs) (projectionValue 2 xs) p'
    have ret := zeroBranchElim (sameOf (.projection 0) (.projection 2)) (.projection 1)
      (succOf (.projection 1)) z xs ct (withHyp h E.not)
    obtain ⟨eq⟩ := valueUnique (.projection 1) previous z xs (projectionValue 1 xs) ret
    exact ⟨Derivation.conjunctionIntroduction p eq⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroStepProof
