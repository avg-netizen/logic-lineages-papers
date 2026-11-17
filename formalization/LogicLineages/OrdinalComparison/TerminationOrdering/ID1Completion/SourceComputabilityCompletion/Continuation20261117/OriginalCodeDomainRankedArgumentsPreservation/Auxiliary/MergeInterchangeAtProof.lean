module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumInterchangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (trans symm)
open InternalAdditionLawsProof (add associativity)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (merge maximum)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atComponents (a b c sa la sb lb sc lc bc ac left right mbc mac ml mr : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing a sa la)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing b sb lb)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing c sc lc)))
    (hbc : Nonempty (Derivation body Delta (graph2 merge bc b c)))
    (hac : Nonempty (Derivation body Delta (graph2 merge ac a c)))
    (hl : Nonempty (Derivation body Delta (graph2 merge left a bc)))
    (hr : Nonempty (Derivation body Delta (graph2 merge right b ac)))
    (hmbc : Nonempty (Derivation body Delta (graph2 maximum mbc lb lc)))
    (hmac : Nonempty (Derivation body Delta (graph2 maximum mac la lc)))
    (hml : Nonempty (Derivation body Delta (graph2 maximum ml la mbc)))
    (hmr : Nonempty (Derivation body Delta (graph2 maximum mr lb mac))) :
    Nonempty (Derivation body Delta (eqn left right)) := by
  have pbc := MergeRecoverProof.pairAtMaximum b c sb lb sc lc mbc bc hb hc hmbc hbc
  have pac := MergeRecoverProof.pairAtMaximum a c sa la sc lc mac ac ha hc hmac hac
  have pl := MergeRecoverProof.pairAtMaximum a bc sa la (add sb sc) mbc ml left ha pbc hml hl
  have pr := MergeRecoverProof.pairAtMaximum b ac sb lb (add sa sc) mac mr right hb pac hmr hr
  have es : Derivation body Delta (eqn (add sa (add sb sc)) (add sb (add sa sc))) :=
    trans (symm (associativity sa sb sc))
      (trans (InternalOriginalOrderProof.congAddRight sc (InternalAdditionCancellationProof.commutativity sa sb))
        (associativity sb sa sc))
  have em := MaximumInterchangeProof.interchange la lb lc mbc mac ml mr hmbc hmac hml hmr
  have pls := headTransport InternalPairing.pairing left (add sa (add sb sc)) (add sb (add sa sc))
    (Fin.cons ml Fin.elim0) ⟨es⟩ pl
  have plr := TransportBaseProof.secondTransport InternalPairing.pairing
    left (add sb (add sa sc)) ml mr em pls
  exact valueUnique InternalPairing.pairing left right ![add sb (add sa sc),mr] plr pr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeAtProof
