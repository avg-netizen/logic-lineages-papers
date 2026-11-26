module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc eqn)
open InternalTagArithmeticSupportProof (symm)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nextCodeValue (stage tab code : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn code (suc stage)))) :
 Nonempty (Derivation body Delta (graph2 nextCode code stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have hs := unaryValue .succ (.projection 0) (suc stage) stage xs
   (successorValue (Fin.cons stage Fin.elim0)) (projectionValue 0 xs)
 obtain ⟨he⟩ := he
 exact outputTransport nextCode (suc stage) code xs ⟨symm he⟩ hs

theorem rootValue (stage tab code base inner root rows : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn code (suc stage))))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows))) :
 Nonempty (Derivation body Delta (graph2 recursiveRoot root stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have hn := nextCodeValue stage tab code he
 have hin := unaryValue InternalUnpair.right nextCode inner code xs (pairRight code base inner ho) hn
 exact unaryValue InternalUnpair.left (rightOf nextCode) root inner xs (pairLeft inner root rows hi) hin

theorem tagValue (stage tab code base inner root rows label data : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn code (suc stage))))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root label data))) :
 Nonempty (Derivation body Delta (graph2 tag label stage tab)) :=
 unaryValue InternalUnpair.left recursiveRoot label root (![stage,tab] : Fin 2 → OTerm alpha)
   (pairLeft root label data hr) (rootValue stage tab code base inner root rows he ho hi)

theorem payloadValue (stage tab code base inner root rows label data : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn code (suc stage))))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root label data))) :
 Nonempty (Derivation body Delta (graph2 payload data stage tab)) :=
 unaryValue InternalUnpair.right recursiveRoot data root (![stage,tab] : Fin 2 → OTerm alpha)
   (pairRight root label data hr) (rootValue stage tab code base inner root rows he ho hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
