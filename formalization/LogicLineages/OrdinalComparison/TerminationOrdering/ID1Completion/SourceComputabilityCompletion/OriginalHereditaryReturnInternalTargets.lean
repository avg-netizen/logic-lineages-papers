module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
/-- Literal constructor-coordinate return laws. Slots are actual supplied values;
no correctness assumption about their computation is used. -/
def VariableLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw index data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 0) index)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data typ index)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 0) data)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def LambdaLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw payload domain childRaw codomain observed typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain childRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ domain codomain)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observed codomain first)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 1) data)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def ApplicationLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw payload domain children fnRaw argRaw fnType fnObserved argObserved observations typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children fnRaw argRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnObserved fnType first)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argObserved domain second)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations fnObserved argObserved)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ observations)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 2) data)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def BottomLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 3) typ)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def OrdinaryLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw payload head baseRaw headObserved sortedBase observations data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload head baseRaw)) →
 Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headObserved head)) →
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sortedBase first)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations headObserved sortedBase)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data typ observations)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 4) data)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def NumberedLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second typ raw payload number headTail head arityTail arityCode children baseRaw extrasRaw headObserved sortedBase observations headData typedData data out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload number headTail)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headTail head arityTail)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing arityTail arityCode children)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children baseRaw extrasRaw)) →
 Nonempty (Derivation body Delta (graph1 OriginalHeadClassNumber.classNumber headObserved head)) →
 Nonempty (Derivation body Delta (graph1 OriginalNumericListSort.sort sortedBase first)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observations sortedBase second)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing headData headObserved observations)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData typ headData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data number typedData)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 5) data)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second))

def ArgumentsConsLaw : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input first second payload typ children headRaw tailRaw observed out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input (numeral 7) payload)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload typ children)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children headRaw tailRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observed typ first)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out observed second)) →
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons out input first second))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalTargets
