module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRootObservation
/-- Actual constructor coordinates and actual R-child computations only.
All graphs are internal derivations; no native calibration or source oracle. -/
def VariableLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter typ raw index data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 0) index)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data typ index)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) data)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

def BottomLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter typ raw out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 3) typ)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

def ApplicationLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter typ raw domain children payload fnRaw argRaw fnType fnPacked argPacked fnValue argValue fnObserved argObserved observations typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children fnRaw argRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnPacked fnType fnRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argPacked domain argRaw)) →
 Nonempty (Derivation body Delta (graph2 R fnValue fnPacked parameter)) →
 Nonempty (Derivation body Delta (graph2 R argValue argPacked parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnObserved fnType fnValue)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argObserved domain argValue)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fnObserved argObserved)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ observations)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 2) data)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

def LambdaLaw : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input parameter arrow raw domain codomain payload childRaw childPacked context gamma extended childParam childValue observed typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input arrow raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain childRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain codomain)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPacked codomain childRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context extended)) →
 Nonempty (Derivation body Delta (graph2 R childValue childPacked childParam)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observed codomain childValue)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) data)) →
 Nonempty (Derivation body Delta (graph2 (rootObservation R) out input parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
