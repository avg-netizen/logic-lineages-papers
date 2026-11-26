module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchFactsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (nilValue nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalTagArithmeticSupportProof (refl sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalLiteralCount (entryCount entryStep)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountOpenConsProof (chosenHead)
open NumberedWindowInternalLiteralSingletonScratchTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_LiteralCountScratchNil (key : OTerm α) :
    Nonempty (Derivation B Γ (counted z key z)) := by
  have value := nilValue (constant 1 0) entryStep (z : OTerm α) ![key]
    (constantZeroValue (body := B) (Gamma := Γ) ![key])
  have tape : (![z,key] : Fin 2 → OTerm α) = Fin.cons z (![key] : Fin 1 → OTerm α) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  simpa only [counted,tape,recGraph,entryCount] using value

theorem exact_NoScratchNilMember (key : OTerm α)
    (present : Nonempty (Derivation B Γ (memberGraph z key))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have wrong := nilRecover memberBase memberStep (suc z) ![key] present
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![key] wrong (constantZeroValue ![key])
  exact ⟨sucNeZeroApply bad⟩

theorem exact_LiteralSingletonCount : ExactLiteralSingletonCount := by
  intro B α Γ code head oneCell
  exact chosenHead code head z head z oneCell (exact_LiteralCountScratchNil head) ⟨refl head⟩

theorem exact_LiteralSingletonMember : ExactLiteralSingletonMember := by
  intro B α Γ code head key oneCell present
  obtain ⟨split⟩ := consInversion code head z key oneCell present
  let L := (missGraph head key).not
  let R := memberGraph z key
  obtain ⟨yes⟩ := equalityOfHit head key (body := B) (Γ := L :: Γ)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := exact_NoScratchNilMember (B := B) (Γ := R :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction (Derivation.explosion bad))⟩

#print axioms exact_LiteralCountScratchNil
#print axioms exact_NoScratchNilMember
#print axioms exact_LiteralSingletonCount
#print axioms exact_LiteralSingletonMember
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchFactsProof
