module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryCheckProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EntryFacts
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem entryIff (H : Program 1) (M W : Program 2) (entry typ term gamma context : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ term))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) entry gamma context)) ↔
    (Nonempty (Derivation body Delta (eqn typ z)) ∧
     Nonempty (Derivation body Delta (programGraph (OriginalUniverseDecoder.termCheck H M W)
       (suc z) ![typ,term,gamma,context]))) := by
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha entry typ term) hp
  let xs : Fin 3 → OTerm alpha := ![entry,gamma,context]
  let L : Program 3 := leftOf (.projection 0)
  let R : Program 3 := rightOf (.projection 0)
  let G : Fin 4 → Program 3 := ![L,R,.projection 1,.projection 2]
  let vs : Fin 4 → OTerm alpha := ![typ,term,gamma,context]
  have hl : Nonempty (Derivation body Delta (programGraph L typ xs)) :=
    unaryValue InternalUnpair.left (.projection 0) typ entry xs ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 xs)
  have hr : Nonempty (Derivation body Delta (programGraph R term xs)) :=
    unaryValue InternalUnpair.right (.projection 0) term entry xs ⟨Derivation.conjunctionRight hi⟩ (projectionValue 0 xs)
  have hargs : ∀ i, Nonempty (Derivation body Delta (programGraph (G i) (vs i) xs)) := by
    intro i
    exact Fin.cases hl (Fin.cases hr (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k)))) i
  constructor
  · intro h
    have hc := InternalAcceptanceConjunctionProof.conjunctionRecover (sameOf L (constant 3 0))
      (.composition (OriginalUniverseDecoder.termCheck H M W) G) xs h
    exact ⟨InternalEqualityTestProof.equalityOfAcceptance typ z
      (binaryRecover InternalEqualityTest.equalityTest L (constant 3 0) (suc z) typ z xs
        (andLeft hc) hl (constantValue 0 xs)),
      compositionRecover (OriginalUniverseDecoder.termCheck H M W) G (suc z) xs vs (andRight hc) hargs⟩
  · rintro ⟨he,ht⟩
    exact InternalAcceptanceConjunctionProof.conjunctionAccept (sameOf L (constant 3 0))
      (.composition (OriginalUniverseDecoder.termCheck H M W) G) xs
      (binaryValue InternalEqualityTest.equalityTest L (constant 3 0) (suc z) typ z xs
        (InternalEqualityTestCompositionProof.equalityOfEqual typ z he) hl (constantValue 0 xs))
      (compositionValue (OriginalUniverseDecoder.termCheck H M W) G (suc z) xs vs ht hargs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryCheckProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryCheckProof
