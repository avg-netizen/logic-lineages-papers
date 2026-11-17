module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountConsTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountKeepAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open EraseInvariant Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCounts (left right head tail rest needle query lc rc tc sc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right query)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail query)))
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count sc rest query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc bit))) ⊓
       ((eqn needle query).not.imp (eqn lc rc)))) := by
  have hyes := CountEffectBindingProof.equalQuery tail needle rest bit query tc sc
    (withHyp h (eqn needle query)) (withHyp ht _) (withHyp hs _)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hy⟩ := CountConsTransportProof.added left right head tail rest query lc rc tc sc bit
    (withHyp hlc _) (withHyp hrc _) (withHyp hl _) (withHyp hr _) (withHyp ht _) (withHyp hs _) hyes
  have hno := CountEffectBindingProof.unequalQuery tail needle rest bit query tc sc
    (withHyp h (eqn needle query).not) (withHyp ht _) (withHyp hs _)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := CountConsTransportProof.equal left right head tail rest query lc rc tc sc
    (withHyp hlc _) (withHyp hrc _) (withHyp hl _) (withHyp hr _) (withHyp ht _) (withHyp hs _) hno
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hy)
    (Derivation.implicationIntroduction hn)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountKeepAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountKeepAtProof
