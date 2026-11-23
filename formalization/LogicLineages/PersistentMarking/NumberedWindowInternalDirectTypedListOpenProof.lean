module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique programRename)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename unaryRename)
open NumberedWindowInternalDirectTypedListTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem payloadPicked (raw decoded : OTerm α)
    (parsed : Nonempty (Derivation B Γ (unary parser (suc decoded) raw))) :
    Nonempty (Derivation B Γ (unary parsedPayload decoded raw)) := by
  apply compositionValue predecessor (Fin.cons parser Fin.elim0) decoded ![raw] ![suc decoded]
    (predecessorSuccessor decoded)
  intro i
  obtain rfl := Fin.eq_zero i
  exact parsed

private theorem typedOnRaw (i : Program 1) (raw decoded : OTerm α)
    (held : Nonempty (Derivation B Γ (unary (typedPayload i) (suc z) raw)))
    (parsed : Nonempty (Derivation B Γ (unary parser (suc decoded) raw))) :
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) decoded)) := by
  apply compositionRecover (typedScratch i) (Fin.cons parsedPayload Fin.elim0)
    (suc z) ![raw] ![decoded] held
  intro k
  obtain rfl := Fin.eq_zero k
  exact payloadPicked raw decoded parsed

theorem exact_OpenJRaw : ExactOpenJRaw := by
  intro i B α Γ raw goal held next
  apply optionGraphCases parser ![raw] goal
  · intro β ρ Δ keep zero
    rw [inputsRename] at zero
    have hr : Nonempty (Derivation B Δ (unary (jRaw i) (suc z) (raw.relabel ρ))) := by
      simpa only [unaryRename,sucRelabel,zRelabel] using renameInto held ρ Δ keep
    have bad := zeroBranchElim parser (constantZero 1) (typedPayload i) (suc z) ![raw.relabel ρ] zero hr
    obtain ⟨e⟩ := valueUnique (constantZero 1) (suc z) z ![raw.relabel ρ] bad
      (constantZeroValue ![raw.relabel ρ])
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩
  · intro β ρ Δ decoded keep parsed
    rw [inputsRename] at parsed
    have hr : Nonempty (Derivation B Δ (unary (jRaw i) (suc z) (raw.relabel ρ))) := by
      simpa only [unaryRename,sucRelabel,zRelabel] using renameInto held ρ Δ keep
    have live := successorBranchElim parser (constantZero 1) (typedPayload i)
      (suc z) decoded ![raw.relabel ρ] parsed hr
    exact next β ρ Δ decoded keep ⟨parsed,typedOnRaw i (raw.relabel ρ) decoded live parsed⟩

theorem exact_IntroJRaw : ExactIntroJRaw := by
  intro i B α Γ raw decoded facts
  apply successorBranchIntro parser (constantZero 1) (typedPayload i) (suc z) decoded ![raw] facts.parsed
  apply compositionValue (typedScratch i) (Fin.cons parsedPayload Fin.elim0)
    (suc z) ![raw] ![decoded] facts.typed
  intro k
  obtain rfl := Fin.eq_zero k
  exact payloadPicked raw decoded facts.parsed

#print axioms exact_OpenJRaw
#print axioms exact_IntroJRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
