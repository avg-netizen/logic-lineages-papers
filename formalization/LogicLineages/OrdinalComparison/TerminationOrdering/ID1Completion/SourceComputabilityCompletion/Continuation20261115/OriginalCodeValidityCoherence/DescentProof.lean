module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.DescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tagGraph (k : Nat) (raw tag payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k)))) :
    Nonempty (Derivation body Delta (graph1 (leftOf (.projection 0)) (numeral k) raw)) := by
  have ht := outputTransport InternalUnpair.left tag (numeral k) (Fin.cons raw Fin.elim0) he
    (pairLeft raw tag payload hp)
  exact unaryValue InternalUnpair.left (.projection 0) (numeral k) raw (Fin.cons raw Fin.elim0)
    ht (projectionValue 0 (Fin.cons raw Fin.elim0))

theorem unary (k : Nat) (hk : k = 1 ∨ k = 4) (raw tag payload first : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k))))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess first raw)) := by
  have ht := tagGraph k raw tag payload hp he
  have ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)) := by
    rcases hk with rfl | rfl
    · exact arityTag1 (.projection 0) (Fin.cons raw Fin.elim0) ht
    · exact arityTag4 (.projection 0) (Fin.cons raw Fin.elim0) ht
  exact unaryChildStrict raw first ha hf

theorem binary (k : Nat) (hk : k = 2 ∨ k = 5 ∨ k = 7) (raw tag payload first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k))))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess first raw ⊓ InternalLessThan.strictLess second raw)) := by
  have ht := tagGraph k raw tag payload hp he
  have ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)) := by
    rcases hk with rfl | rfl | rfl
    · exact arityTag2 (.projection 0) (Fin.cons raw Fin.elim0) ht
    · exact arityTag5 (.projection 0) (Fin.cons raw Fin.elim0) ht
    · exact arityTag7 (.projection 0) (Fin.cons raw Fin.elim0) ht
  exact binaryChildrenStrict raw first second ha hf hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.DescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.DescentProof
