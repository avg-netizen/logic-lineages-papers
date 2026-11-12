module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsPairQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsInternalStepProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem reversedAtNil (R : Program 2) (state raw parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hn : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
 Nonempty (Derivation body Delta (graph2 (reversedObservations R) z raw parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![raw,parameter]
 have hi := binaryValue InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 2 0)
   state raw z xs hp (projectionValue 0 xs) (constantValue 0 xs)
 have hf := unaryValue (body := body) (Gamma := Delta) .succ (.projection (0 : Fin 2)) (suc raw) raw xs
   (successorValue ![raw]) (projectionValue 0 xs)
 have hw : Nonempty (Derivation body Delta (graph3 (walk R) state (suc raw) state parameter)) :=
   OriginalUniverseDecoderInternalFuelNumericFixedProof.fixedValue (walkStep R) (suc raw) state parameter
     (stepNil R state raw z parameter hp hn)
 have hrun : Nonempty (Derivation body Delta (graph2 (walked R) state raw parameter)) := by
   apply compositionValue (walk R) ![OriginalRawSyntaxTransport.succOf (.projection 0),initial,.projection 1]
     state xs ![suc raw,state,parameter] hw
   intro i
   exact Fin.cases hf (Fin.cases hi (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i
 exact unaryValue InternalUnpair.right (walked R) z state xs (pairRight state raw z hp) hrun

theorem reverseAtZero (state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z z))) :
 Nonempty (Derivation body Delta (graph1 reverse z z)) := by
 let xs : Fin 1 → OTerm alpha := ![z]
 have hf : Nonempty (Derivation body Delta (graph1 reverseStep state state)) :=
   InternalAcceptanceBranchProof.zeroBranchIntro reverseRemaining (.projection 0) reverseAdvance state ![state]
     (pairLeft state z z hp) (projectionValue 0 ![state])
 have hrun : Nonempty (Derivation body Delta (graph2 reverseRun state (suc z) state)) :=
   InternalNumericIterationFixedPointProof.fixedValue reverseStep (suc z) state hf
 have hs := unaryValue (body := body) (Gamma := Delta) .succ (.projection (0 : Fin 1)) (suc z) z xs
   (successorValue ![z]) (projectionValue 0 xs)
 have hi := binaryValue InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)
   state z z xs hp (projectionValue 0 xs) (constantValue 0 xs)
 have hv := binaryValue reverseRun (OriginalRawSyntaxTransport.succOf (.projection 0))
   (pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)) state (suc z) state xs hrun hs hi
 exact unaryValue InternalUnpair.right
   (.composition reverseRun ![OriginalRawSyntaxTransport.succOf (.projection 0),pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)])
   z state xs (pairRight state z z hp) hv

attribute [local irreducible] reverse argumentObservations reversedObservations walk walked

theorem reverseZero : Nonempty (Derivation body Delta (graph1 reverse z z)) :=
 OriginalTypedArgumentObservationsPairQueryProof.unaryZero reverse
   (fun _ _ state hp => reverseAtZero state hp)

theorem nilValue (R : Program 2) (raw parameter : OTerm alpha)
 (hn : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) z raw parameter)) := by
 apply OriginalTypedArgumentObservationsPairQueryProof.binaryZero (argumentObservations R)
   OriginalRawSyntaxTransport.nilConstructor raw parameter hn
 intro beta Theta state r c hp hq
 have hr := reversedAtNil R state r c hp hq
 simpa only [argumentObservations] using
   (unaryValue reverse (reversedObservations R) z z ![r,c] reverseZero hr)

theorem internalNil : OriginalTypedArgumentObservationsTargets.InternalNil := by
 intro R body alpha raw parameter out
 let H := programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0
 let P := graph2 (argumentObservations R) out raw parameter
 let Q := equal out z
 have hv : Nonempty (Derivation body [H] (graph2 (argumentObservations R) z raw parameter)) :=
   nilValue R raw parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hf : Nonempty (Derivation body (P :: [H]) Q) := by
   have hz := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hv P
   simpa only [Q,InternalControlGraphSupportProof.equalEqn] using
     (valueUnique (argumentObservations R) out z ![raw,parameter]
       (show Nonempty (Derivation body (P :: [H]) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩) hz)
 have hb : Nonempty (Derivation body (Q :: [H]) P) := by
   have hz := InternalApplicationValidityStackAppendInductionCoreProof.withHyp hv Q
   have he : Nonempty (Derivation body (Q :: [H]) (eqn out z)) := by
     simpa only [Q,InternalControlGraphSupportProof.equalEqn] using
       (show Nonempty (Derivation body (Q :: [H]) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   obtain ⟨he⟩ := he
   exact outputTransport (argumentObservations R) z out ![raw,parameter]
     ⟨InternalTagArithmeticSupportProof.symm he⟩ hz
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.implicationIntroduction
   (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
