module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalRawChildTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalOrderSyntaxProof
open OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof (numeral)
/-- Exact registration of the independently checked literal raw-child branches.
These are not yet bounded lookup inversion or the full expansion endpoint. -/
def RawSecond : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))),
 Nonempty (Derivation body Delta (ltF V W))
def RawFirstBinary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))),
 Nonempty (Derivation body Delta (ltF V W))
def RawFirstUnary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))),
 Nonempty (Derivation body Delta (ltF V W))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalRawChildTargets
