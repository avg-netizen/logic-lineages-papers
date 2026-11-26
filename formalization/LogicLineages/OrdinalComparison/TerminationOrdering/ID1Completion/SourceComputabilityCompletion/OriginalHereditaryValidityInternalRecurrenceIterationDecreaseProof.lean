module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem liveFromState (state workCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hn : Nonempty (Derivation body Gamma (eqn workCode z).not)) :
    Nonempty (Derivation body Gamma (LiveWork state)) := by
  let A := graph1 work z state
  have hp := pairRight state (numeral 1) workCode hs
  have he := valueUnique work workCode z (Fin.cons state Fin.elim0)
    (weakenProof hp (fun q hq => List.mem_cons_of_mem A hq))
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn⟩ := weakenProof hn (fun q hq => List.mem_cons_of_mem A hq)
  obtain ⟨he⟩ := he
  exact andIntro (pairLeft state (numeral 1) workCode hs)
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn he)⟩

/-- Eliminate only the witnesses already constructed by the exact internal
decrease theorem. Neither branch assumes a completed iteration. -/
theorem decreasedCases (out previous : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (DecreasedOrFailed out previous)))
    (failure : ∀ (Delta : List (Formula alpha)), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (equal out z)) → Nonempty (Derivation body Delta psi))
    (live : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (nextWork nextFuel : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StateGraph (out.relabel j) (numeral 1) nextWork)) →
      Nonempty (Derivation body Delta (WorkFuelGraph nextFuel nextWork)) →
      Nonempty (Derivation body Delta (InternalLessThan.strictLess nextFuel (previous.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let A := equal out z
  let B := InternalFiniteBlocks.block (decreasedBody out previous)
  obtain ⟨ha⟩ := failure (A :: Gamma) (fun p hp => List.mem_cons_of_mem A hp)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: Gamma) psi) := by
    apply InternalFiniteBlocksProof.elimination body alpha 2 (B :: Gamma)
      (decreasedBody out previous) psi ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply live (alpha ⊕ Fin 2) Sum.inl
      (decreasedBody out previous :: (B :: Gamma).map (fun p => p.relabel Sum.inl))
      (.var (.inr 0)) (.var (.inr 1))
    · intro p hp
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,List.mem_cons_of_mem B hp,rfl⟩)
    · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    · exact ⟨Derivation.conjunctionLeft
        (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    · exact ⟨Derivation.conjunctionRight
        (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  obtain ⟨h⟩ := h
  obtain ⟨hb⟩ := hb
  exact ⟨disjunctionElimination h
    (Derivation.implicationIntroduction ha) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
