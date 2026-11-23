module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityCountProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAdditionLawsProof (leftSuccessor)
open ID1Completion.InternalTagArithmeticSupportProof (addSucc cancelSuc trans zeroNeSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountZeroChecks (exact_OpenLiteralZeroCountAbsent)
open NumberedWindowInternalLiteralCountAllQueries (eachAtPermutation)
open NumberedWindowInternalLiteralCountAppendProof (exact_LiteralOpenCountAppend)
open NumberedWindowInternalLiteralSingletonCapacityTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveHeld {β : Type} (src q kept rem joined : OTerm α)
    (held : Held B Γ src q kept rem joined)
    (ρ : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel ρ ∈ Δ) :
    Held B Δ (src.relabel ρ) (q.relabel ρ) (kept.relabel ρ) (rem.relabel ρ) (joined.relabel ρ) := by
  constructor
  · simpa only [countedRename,sucRelabel,zRelabel] using renameInto held.singletonCount ρ Δ keep
  · simpa only [appendRename] using renameInto held.sourceAppend ρ Δ keep
  · simpa only [observed,sucRelabel,zRelabel] using
      renamePair permutation (suc z) src joined held.countObserved ρ keep

private theorem positiveCountCases (list key : OTerm α)
    (member : Nonempty (Derivation B Γ (memberGraph list key)))
    (next : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (pred : OTerm β),
      (∀ p ∈ Γ, p.relabel ρ ∈ Δ) →
      Nonempty (Derivation B Δ (counted (list.relabel ρ) (key.relabel ρ) (suc pred))) →
      Nonempty (Derivation B Δ (⊥ : Formula β))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  apply optionGraphCases entryCount ![list,key] (⊥ : Formula α)
  · intro β ρ Δ keep zero
    rw [binaryInputsRename] at zero
    have m' := renameInto member ρ Δ keep
    rw [graphRename] at m'
    obtain ⟨occurs⟩ := m'
    obtain ⟨zero⟩ := zero
    obtain ⟨law⟩ := exact_OpenLiteralZeroCountAbsent B β Δ (list.relabel ρ) (key.relabel ρ)
    exact ⟨Derivation.implicationElimination (Derivation.implicationElimination law zero) occurs⟩
  · intro β ρ Δ pred keep yes
    rw [binaryInputsRename] at yes
    exact next β ρ Δ pred keep yes

private theorem arithmeticCapacity (src q kept rem joined l r out : OTerm α)
    (held : Held B Γ src q kept rem joined)
    (cl : Nonempty (Derivation B Γ (counted kept q (suc l))))
    (cr : Nonempty (Derivation B Γ (counted rem q (suc r))))
    (cj : Nonempty (Derivation B Γ (counted joined q out))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨one⟩ := eachAtPermutation src joined q (suc z) out held.countObserved held.singletonCount cj
  obtain ⟨sum⟩ := exact_LiteralOpenCountAppend kept rem q joined (suc l) (suc r) out held.sourceAppend cl cr cj
  have clash := cancelSuc (trans one (trans sum (leftSuccessor l (suc r))))
  exact ⟨zeroNeSuc (trans clash (addSucc l r))⟩

private theorem chooseJoined (src q kept rem joined l r : OTerm α)
    (held : Held B Γ src q kept rem joined)
    (cl : Nonempty (Derivation B Γ (counted kept q (suc l))))
    (cr : Nonempty (Derivation B Γ (counted rem q (suc r)))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  apply programCases entryCount ![joined,q] (⊥ : Formula α)
  intro β ρ Δ out keep ran
  rw [binaryInputsRename] at ran
  have cl' : Nonempty (Derivation B Δ (counted (kept.relabel ρ) (q.relabel ρ) (suc (l.relabel ρ)))) := by
    simpa only [countedRename,sucRelabel] using renameInto cl ρ Δ keep
  have cr' : Nonempty (Derivation B Δ (counted (rem.relabel ρ) (q.relabel ρ) (suc (r.relabel ρ)))) := by
    simpa only [countedRename,sucRelabel] using renameInto cr ρ Δ keep
  exact arithmeticCapacity (src.relabel ρ) (q.relabel ρ) (kept.relabel ρ) (rem.relabel ρ)
    (joined.relabel ρ) (l.relabel ρ) (r.relabel ρ) out (moveHeld src q kept rem joined held ρ Δ keep) cl' cr' ran

/-- A physical counted source at one occurrence cannot accommodate two
actual occurrences of that same needle in its two appended operands. -/
theorem exact_LiteralSingletonCapacityAtNeedle (src q kept rem joined : OTerm α)
    (held : Held B Γ src q kept rem joined)
    (left : Nonempty (Derivation B Γ (memberGraph kept q)))
    (right : Nonempty (Derivation B Γ (memberGraph rem q))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  apply positiveCountCases kept q left
  intro β ρ Δ l keep cl
  let S := src.relabel ρ
  let Q := q.relabel ρ
  let K := kept.relabel ρ
  let R := rem.relabel ρ
  let J := joined.relabel ρ
  have h := moveHeld src q kept rem joined held ρ Δ keep
  have r' := renameInto right ρ Δ keep
  rw [graphRename] at r'
  apply positiveCountCases R Q r'
  intro γ τ Ω r retain cr
  have cl' : Nonempty (Derivation B Ω (counted (K.relabel τ) (Q.relabel τ) (suc (l.relabel τ)))) := by
    simpa only [K,Q,countedRename,sucRelabel] using renameInto cl τ Ω retain
  exact chooseJoined (S.relabel τ) (Q.relabel τ) (K.relabel τ) (R.relabel τ) (J.relabel τ)
    (l.relabel τ) r (moveHeld S Q K R J h τ Ω retain) cl' cr

#print axioms exact_LiteralSingletonCapacityAtNeedle
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityCountProof
