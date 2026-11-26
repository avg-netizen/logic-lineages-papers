module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalEnumerationMembership.GuardChoiceProof (orConclusion)
open Continuation20261115 DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem allowed (f : Frame n H arguments body alpha Delta) (tag payload first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second f.raw)))
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  have h0 := ClauseLeafProof.atVariable f tag payload hp
  have h1 := ClauseUnaryProof.atLambda f tag payload first head hp hf
  have h2 := ClauseBinaryProof.atBinary f tag payload first second hp hf hs
  have h3 := ClauseLeafProof.atBottom f tag payload hp
  have h4 := ClauseUnaryProof.atOrdinary f tag payload first head hp hf
  have h5 := ClauseNumberedProof.atNumbered f tag payload first second head hp hf hs
  have h6 := ClauseLeafProof.atNil f tag payload hp
  have h : Nonempty (Derivation body Delta
      ((OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head).imp f.conclusion)) :=
    orConclusion (orConclusion h0 h3) (orConclusion h1 (orConclusion h2 (orConclusion h4 (orConclusion h5 h6))))
  exact ⟨Derivation.implicationElimination (Classical.choice h) (Classical.choice ha)⟩

theorem atFrame (f : Frame n H arguments body alpha Delta) :
    Nonempty (Derivation body Delta f.conclusion) := by
  apply OriginalEnumerationMembership.GuardObservationProof.cases n f.raw f.conclusion f.guard
  intro beta j Theta tag payload first second head hj hp hf hs hh ha
  rw [conclusionRename f j Theta hj]
  exact allowed (f.rename j Theta hj) tag payload first second head hp hf hs ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchProof
