module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Internal counterpart of native root substitution at all six original term
constructors. Only actual original input/parameter/child/list computations and
an actual returnRoot graph are premises. Numeric head classes, sorting and output
pair coordinates must be queried internally. This is a local algebra supplier,
not an assumption that an evaluator run has produced the child results. -/
def Variable : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw index first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 0) index)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

def Bottom : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

def Lambda : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw payload domain childRaw codomain childPacked context gamma extended childParam first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain childRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ domain codomain)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPacked codomain childRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context extended)) →
  Nonempty (Derivation body Delta (graph2 Q first childPacked childParam)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

def Application : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw payload domain children fnRaw argRaw fnType fnPacked argPacked first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children fnRaw argRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnPacked fnType fnRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argPacked domain argRaw)) →
  Nonempty (Derivation body Delta (graph2 Q first fnPacked parameter)) →
  Nonempty (Derivation body Delta (graph2 Q second argPacked parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

def Ordinary : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw payload head base first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload head base)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) first base parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

def Numbered : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields base afterBase extraTypes extras first second returned : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields base afterBase)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) first base parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) second extras parameter)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)) →
  Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionTargets
