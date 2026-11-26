module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplication
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Read the constructor tag of the ORIGINAL Object's raw right payload.
This observer is not installed in the selected source or computability tuple. -/
def objectTag : Program 1 :=
  .composition OriginalConstructorShape.tag (fun _ : Fin 1 => InternalUnpair.right)

abbrev nonLambdaObject {alpha : Type} (object : OTerm alpha) : Formula alpha :=
  (graph1 objectTag InternalOriginalStepGuard.one object).not

/-- The original accepted Object application exposes ONE common runtime
Gamma and the requested RAW function and argument. Its output and symbolic
parameter remain literal original pair graphs. Both the full original
application premises and the weaker typed-neutral input premises are paid
internally, including window activation and codomain membership. The
non-lambda equivalence transports a supplied Object premise to its raw
payload; it adds no non-lambda premise to this exposure theorem. -/
def Recovered {alpha : Type} (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter :
      OTerm alpha) : Formula alpha :=
  InternalComputabilityDownward.domain comp context sigma tau functionObject argumentObject ⊓
    (InternalComputabilityApplication.accepted comp sigma tau (numeral context)
        functionObject argumentObject outputObject ⊓
      (graph2 InternalPairing.pairing functionObject gammaCode function ⊓
        (graph2 InternalPairing.pairing argumentObject gammaCode argument ⊓
          (graph2 InternalPairing.pairing outputObject gammaCode out ⊓
            (graph2 InternalPairing.pairing parameter (numeral context) gammaCode ⊓
              (InternalOriginalUniformApplicationTyping.applicationPremises data
                  (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
                  (numeral (typeNumber tau)) function argument out parameter ⊓
                (OriginalNeutralApplication.InputPremises data window
                    (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma))
                    (numeral (typeNumber tau)) function argument parameter ⊓
                  (InternalParameterizedCanonicalResultFold.applicationGraph data out
                      (numeral (typeNumber sigma)) (numeral (typeNumber tau)) function argument parameter ⊓
                    ((nonLambdaObject functionObject).iff
                      (OriginalNonLambdaApplication.nonLambda function))))))))))

/-- Eliminate only the original typed/guard domain and accepted application.
All coordinates are internally bound. The raw argument is not replaced by a
folded value, and the ORIGINAL accepted output is not supplied a pair shape. -/
def ApplicationInputs (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (sigma tau : Ty) (functionObject argumentObject outputObject : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (InternalComputabilityDownward.domain comp context sigma tau functionObject argumentObject)) →
  Nonempty (Derivation body Gamma
    (InternalComputabilityApplication.accepted comp sigma tau (numeral context)
      functionObject argumentObject outputObject)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ gammaCode function argument out parameter : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered data window comp context sigma tau
        (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
        gammaCode function argument out parameter)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplication
