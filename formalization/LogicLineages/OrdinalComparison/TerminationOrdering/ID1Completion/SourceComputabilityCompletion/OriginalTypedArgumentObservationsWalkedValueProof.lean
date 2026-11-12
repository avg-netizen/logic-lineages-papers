module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsFuelEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkedValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedArgumentObservations
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem initialValue (state raw parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z))) :
 Nonempty (Derivation body Delta (graph2 initial state raw parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 exact binaryValue InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
   state raw z xs hp (projectionValue 0 xs) (constantValue 0 xs)

theorem walkedValue (R : Program 2) (state raw parameter out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out (suc raw) state parameter))) :
 Nonempty (Derivation body Delta (graph2 (walked R) out raw parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 have hi := initialValue state raw parameter hp
 have hf := unaryValue (body := body) (Gamma := Delta) .succ (.projection (0 : Fin 2)) (suc raw) raw xs
   (successorValue (Fin.cons raw Fin.elim0)) (projectionValue 0 xs)
 apply compositionValue (walk R) ![OriginalRawSyntaxTransport.succOf (.projection 0),initial,.projection 1]
   out xs ![suc raw,state,parameter] hr
 intro i
 exact Fin.cases hf (Fin.cases hi (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem reversedValue (R : Program 2) (state raw parameter out remaining value : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out (suc raw) state parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out remaining value))) :
 Nonempty (Derivation body Delta (graph2 (reversedObservations R) value raw parameter)) := by
 exact unaryValue InternalUnpair.right (walked R) value out
   (Fin.cons raw (Fin.cons parameter Fin.elim0)) (pairRight out remaining value ho)
   (walkedValue R state raw parameter out hp hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkedValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkedValueProof
