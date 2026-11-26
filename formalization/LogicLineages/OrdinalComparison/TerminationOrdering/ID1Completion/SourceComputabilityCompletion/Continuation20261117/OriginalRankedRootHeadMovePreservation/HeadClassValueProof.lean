module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadClassValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem chooseEqual (k : Nat) (yes no : Program 1) (raw tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k))))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.choose k yes no) out raw))) :
    Nonempty (Derivation body Delta (graph1 yes out raw)) := by
  have hc := binaryValue InternalEqualityTest.equalityTest InternalUnpair.left (constant 1 k)
    (suc z) tag (numeral k) ![raw]
    (InternalEqualityTestCompositionProof.equalityOfEqual tag (numeral k) he) ht (constantValue k ![raw])
  exact successorBranchElim (sameOf InternalUnpair.left (constant 1 k)) no yes out z ![raw] hc hv

theorem chooseUnequal (k : Nat) (yes no : Program 1) (raw tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral k)).not))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.choose k yes no) out raw))) :
    Nonempty (Derivation body Delta (graph1 no out raw)) := by
  have he' : Nonempty (Derivation body Delta (equal tag (numeral k)).not) := by
    rw [equalEqn]
    exact he
  have hc := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    InternalUnpair.left (constant 1 k) tag (numeral k) ![raw] ht (constantValue k ![raw]) he'
  exact zeroBranchElim (sameOf InternalUnpair.left (constant 1 k)) no yes out ![raw] hc hv

theorem rankedValue (raw symbol : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) symbol))) :
    Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass (suc (suc symbol)) raw)) := by
  apply (OriginalHeadClass.InternalProof.internalTagFactor body alpha Delta ⟨5,by decide⟩ raw symbol (suc (suc symbol)) hp).mpr
  have h1 : Nonempty (Derivation body Delta (graph1 (succOf (.projection 0)) (suc symbol) symbol)) := unaryValue .succ (.projection 0) (suc symbol) symbol ![symbol]
    (successorValue ![symbol]) (projectionValue 0 ![symbol])
  exact unaryValue .succ (succOf (.projection 0)) (suc (suc symbol)) (suc symbol) ![symbol]
    (successorValue ![suc symbol]) h1

theorem applicationValue (raw tag payload out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (eqn tag (numeral 4))))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass out raw))) :
    Nonempty (Derivation body Delta (eqn out (suc z))) := by
  have hy := chooseEqual 4 (OriginalHeadClass.atPayload 4)
    (OriginalHeadEncodingBridge.choose 5 (OriginalHeadClass.atPayload 5) (constant 1 0)) raw tag out
    (pairLeft raw tag payload hp) he hv
  have ho := unaryRecover (OriginalHeadClass.branchClass 4) InternalUnpair.right out payload ![raw] hy (pairRight raw tag payload hp)
  exact valueUnique (constant 1 1) out (suc z) ![payload] ho (constantValue 1 ![payload])

theorem otherValue (raw tag payload out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (h4 : Nonempty (Derivation body Delta (eqn tag (numeral 4)).not))
    (h5 : Nonempty (Derivation body Delta (eqn tag (numeral 5)).not))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass out raw))) :
    Nonempty (Derivation body Delta (eqn out z)) := by
  have ht := pairLeft raw tag payload hp
  have h := chooseUnequal 4 (OriginalHeadClass.atPayload 4)
    (OriginalHeadEncodingBridge.choose 5 (OriginalHeadClass.atPayload 5) (constant 1 0)) raw tag out ht h4 hv
  have h0 := chooseUnequal 5 (OriginalHeadClass.atPayload 5) (constant 1 0) raw tag out ht h5 h
  exact valueUnique (constant 1 0) out z ![raw] h0 (constantValue 0 ![raw])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadClassValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadClassValueProof
