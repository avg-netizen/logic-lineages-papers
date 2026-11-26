module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual state/control coordinates and exact runtime selector graphs. No desired
step graph, source validity, native reflection or semantic Expected premise. -/
def TermLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload packed parameter first second row old root returned tail value stack out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.firstSlot first input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.secondSlot second input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.deletionRow row input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.oldSuffix old input)) →
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first second)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))

def ListNilLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload old stack out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.raw raw input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.oldSuffix old input)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack (numeral 0) old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))

def ListConsLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results frame rest payload raw rawPayload first second old value stack out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 1) input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.raw raw input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.firstSlot first input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.secondSlot second input)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.oldSuffix old input)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons value raw first second)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out rest stack)) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalTargets
