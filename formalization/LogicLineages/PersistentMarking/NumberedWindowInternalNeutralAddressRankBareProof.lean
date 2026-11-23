module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankBareProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalFixedWindowVertexDispatch (constant)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenAtomicRecognition)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalNeutralAddressRank (addressRank)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An actual bare free leaf has a true open rank report. No reflection
from numeric behavior of the raw evaluator is assumed. -/
theorem exact_OpenAddressRankBareFree (raw : Program 1) (x ctx t name : OTerm α)
    (shape : Nonempty (Derivation B Γ (equal x (packedFreeTerm ctx t name)))) :
    Nonempty (Derivation B Γ (unary (addressRank raw) (suc (suc z)) x)) := by
  let a := branch addressGood (constantZero 1) (applyUnary raw rawLeast)
  let b := branch bottomSource a (constant 1 1)
  obtain ⟨h⟩ := exact_OpenAtomicRecognition.1 B α Γ x ctx t name shape
  change Nonempty (Derivation B Γ
    (programGraph (branch freeSource b (constant 1 2)) (suc (suc z)) ![x]))
  exact successorBranchIntro freeSource b (constant 1 2) (suc (suc z)) z ![x]
    ⟨Derivation.conjunctionLeft h⟩ (constantValue 1 2 ![x])

/-- Bare bottom reports positive rank one, not the rejected rank zero. -/
theorem exact_OpenAddressRankBareBottom (raw : Program 1) (x ctx t : OTerm α)
    (shape : Nonempty (Derivation B Γ (equal x (packedBottomTerm ctx t)))) :
    Nonempty (Derivation B Γ (unary (addressRank raw) (suc z) x)) := by
  let a := branch addressGood (constantZero 1) (applyUnary raw rawLeast)
  let b := branch bottomSource a (constant 1 1)
  obtain ⟨h⟩ := exact_OpenAtomicRecognition.2 B α Γ x ctx t shape
  change Nonempty (Derivation B Γ
    (programGraph (branch freeSource b (constant 1 2)) (suc z) ![x]))
  exact zeroBranchIntro freeSource b (constant 1 2) (suc z) ![x] ⟨Derivation.conjunctionLeft h⟩
    (successorBranchIntro bottomSource a (constant 1 1) (suc z) z ![x]
      ⟨Derivation.conjunctionRight h⟩ (constantValue 1 1 ![x]))

#print axioms exact_OpenAddressRankBareFree
#print axioms exact_OpenAddressRankBareBottom
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankBareProof
