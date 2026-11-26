module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open ObservationDescentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem nilValue (input : OTerm alpha) :
 Nonempty (Derivation body Delta (graph1 (select []) input input)) :=
 projectionValue 0 (Fin.cons input Fin.elim0)

theorem rightValue (path : List Bool) (input left right out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input left right)))
 (hs : Nonempty (Derivation body Delta (graph1 (select path) out right))) :
 Nonempty (Derivation body Delta (graph1 (select (true :: path)) out input)) :=
 unaryValue (select path) InternalUnpair.right out right (Fin.cons input Fin.elim0)
   hs (pairRight input left right hp)

theorem leftValue (path : List Bool) (input left right out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input left right)))
 (hs : Nonempty (Derivation body Delta (graph1 (select path) out left))) :
 Nonempty (Derivation body Delta (graph1 (select (false :: path)) out input)) :=
 unaryValue (select path) InternalUnpair.left out left (Fin.cons input Fin.elim0)
   hs (pairLeft input left right hp)

theorem lambdaValue (data domain typedData codomain observed : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observed))) :
 Nonempty (Derivation body Delta (graph1 (select (directPath .lambdaBody)) observed data)) :=
 rightValue [true] data domain typedData observed hd
   (rightValue [] typedData codomain observed observed ht (nilValue observed))

theorem functionValue (data domain typedData codomain observations fn arg : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observations)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fn arg))) :
 Nonempty (Derivation body Delta (graph1 (select (directPath .function)) fn data)) :=
 rightValue [true,false] data domain typedData fn hd
   (rightValue [false] typedData codomain observations fn ht
     (leftValue [] observations fn arg fn hc (nilValue fn)))

theorem argumentValue (data domain typedData codomain observations fn arg : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observations)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fn arg))) :
 Nonempty (Derivation body Delta (graph1 (select (directPath .argument)) arg data)) :=
 rightValue [true,true] data domain typedData arg hd
   (rightValue [true] typedData codomain observations arg ht
     (rightValue [] observations fn arg arg hc (nilValue arg)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
