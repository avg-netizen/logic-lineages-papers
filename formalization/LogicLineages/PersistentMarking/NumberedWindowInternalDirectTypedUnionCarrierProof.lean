module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstalledCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectTypedListTargets (jRaw typedPayload parsedPayload)
open NumberedWindowInternalDirectTypedListInstalledCarrierProof (exact_IntroInstalledTypedCarrier)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectSourcePartitionRawTargets (observePartition)
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedUnionScratchProof (exact_TypedUnionScratch)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (oddCarrierRename)
open NumberedWindowInternalDirectTypedUnionCarrierTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At a genuine original parser success already chosen by the held union,
recover jRaw's typed scratch on that **same** value, using its actual branch. -/
private theorem typingAtKnownPayload (i : Program 1) (raw out : OTerm α)
    (accepted : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) raw)))
    (parsed : Nonempty (Derivation B Γ (unary parser (suc out) raw))) :
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) out)) := by
  have ran := successorBranchElim parser (constantZero 1) (typedPayload i)
    (suc z) out ![raw] parsed accepted
  have actual : Nonempty (Derivation B Γ (unary parsedPayload out raw)) := by
    apply compositionValue predecessor (Fin.cons parser Fin.elim0) out ![raw] ![suc out]
      (predecessorSuccessor out)
    intro j
    obtain rfl := Fin.eq_zero j
    exact parsed
  apply compositionRecover (typedScratch i) (Fin.cons parsedPayload Fin.elim0)
    (suc z) ![raw] ![out] ran
  intro j
  obtain rfl := Fin.eq_zero j
  exact actual

theorem exact_SelectedUnionCarrierSupply : ExactSelectedUnionCarrierSupply := by
  intro i r count c
  dsimp only
  intro support α Γ a b u ca cb unionHeld
  let S := data i (jRaw i) r (dCore i r count)
  let B := sourceBody S c
  have rawA : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) a)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r count) true c B α Γ a).1 ca
  have rawB : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) b)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r count) true c B α Γ b).1 cb
  apply exact_OpenRawSourceDecode (observePartition count) B α Γ u a b (carrier S true c u) unionHeld
  intro β ρ Δ su sa sb keep parsed accepted
  rw [oddCarrierRename]
  have a' : Nonempty (Derivation B Δ (unary (jRaw i) (suc z) (a.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto rawA ρ Δ keep
  have b' : Nonempty (Derivation B Δ (unary (jRaw i) (suc z) (b.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto rawB ρ Δ keep
  have ta := typingAtKnownPayload i (a.relabel ρ) sa a' parsed.kept
  have tb := typingAtKnownPayload i (b.relabel ρ) sb b' parsed.removed
  apply exact_OpenSourcePartitionAppend count su sa sb (carrier S true c (u.relabel ρ)) accepted
  intro γ τ Ω joined retain appended observed
  rw [oddCarrierRename]
  have ua := renameParser (u.relabel ρ) su parsed.source τ Ω retain
  have la : Nonempty (Derivation B Ω (unary (typedScratch i) (suc z) (sa.relabel τ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto ta τ Ω retain
  have rb : Nonempty (Derivation B Ω (unary (typedScratch i) (suc z) (sb.relabel τ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto tb τ Ω retain
  have ut := exact_TypedUnionScratch i count B γ Ω (sa.relabel τ) (sb.relabel τ) (su.relabel τ)
    joined support la rb appended observed
  exact exact_IntroInstalledTypedCarrier i r count c γ Ω ((u.relabel ρ).relabel τ) (su.relabel τ) ⟨ua,ut⟩

#print axioms exact_SelectedUnionCarrierSupply
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierProof
