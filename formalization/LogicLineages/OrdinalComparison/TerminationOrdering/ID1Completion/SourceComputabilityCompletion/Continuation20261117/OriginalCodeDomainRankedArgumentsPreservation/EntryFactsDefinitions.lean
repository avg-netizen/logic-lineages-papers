module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFacts
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Auxiliary concrete entry check at [encoded(type,term),Gamma,Context].
This is a proof invariant only; the final checker AST is unchanged. -/
def entryCheck (H : Program 1) (M W : Program 2) : Program 3 :=
  InternalAcceptance.conjunction
    (sameOf (leftOf (.projection 0)) (constant 3 0))
    (.composition (OriginalUniverseDecoder.termCheck H M W)
      ![leftOf (.projection 0),rightOf (.projection 0),.projection 1,.projection 2])
def query {alpha : Type} (entries needle hits : OTerm alpha) : Formula alpha :=
  graph2 Continuation20261114.ArgumentEntryCount.count hits entries needle ⊓ (eqn hits z).not
def matrix {alpha : Type} (H : Program 1) (M W : Program 2)
    (entries gamma context : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (query (entries.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (graph3 (entryCheck H M W) (suc z) (.var (.inr 0)) (gamma.relabel Sum.inl) (context.relabel Sum.inl))
def allGood {alpha : Type} (H : Program 1) (M W : Program 2)
    (entries gamma context : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix H M W entries gamma context)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFacts
