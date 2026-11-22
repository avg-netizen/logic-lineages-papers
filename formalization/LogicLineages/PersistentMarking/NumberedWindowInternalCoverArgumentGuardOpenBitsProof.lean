module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenBitsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentCell)
open NumberedWindowInternalCoverArgumentGuardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualGuardAccepted (G : Program 1) (prior old : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (argumentRejectUpdate G) z ![prior,old,z,z]))) :
    Nonempty (Derivation body Γ (programGraph (argumentGuard G) (suc z) ![prior,old,z,z])) := by
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  let C := argumentGuard G
  let Q := programGraph C (suc z) xs
  apply formulaCases Q Q
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have failed := normalizeReject (body := body) (Gamma := Q.not :: Γ) C xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have wrong := zeroBranchElim (normalize C) (literal 4 1) (constantZero 4) z xs failed
      (withHyp actual Q.not)
    obtain ⟨no⟩ := valueUnique (literal 4 1) (suc z) z xs (literalGraph 1 xs) wrong
    exact ⟨Derivation.explosion (sucNeZeroApply no)⟩

theorem actualArgumentGuardBits (G : Program 1) (prior old : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (argumentRejectUpdate G) z ![prior,old,z,z]))) :
    Nonempty (Derivation body Γ (programGraph argumentCell (suc z) ![prior,old,z,z])) ∧
    Nonempty (Derivation body Γ (programGraph (argumentHeadAccept G) (suc z) ![prior,old,z,z])) ∧
    Nonempty (Derivation body Γ (programGraph argumentTailAccept (suc z) ![prior,old,z,z])) := by
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  obtain ⟨top⟩ := conjunctionRecover argumentCell
    (ID1Completion.InternalAcceptance.conjunction (argumentHeadAccept G) argumentTailAccept)
    xs (actualGuardAccepted G prior old actual)
  obtain ⟨both⟩ := conjunctionRecover (argumentHeadAccept G) argumentTailAccept xs
    ⟨Derivation.conjunctionRight top⟩
  exact ⟨⟨Derivation.conjunctionLeft top⟩,⟨Derivation.conjunctionLeft both⟩,⟨Derivation.conjunctionRight both⟩⟩

#print axioms actualGuardAccepted
#print axioms actualArgumentGuardBits

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenBitsProof
