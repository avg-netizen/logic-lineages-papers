module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObject
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2 pairOf leftOf rightOf)
open InternalParameterizedCanonicalResultFold (foldGraph foldN)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal Program wrapper with inputs [outer Context, original Object].
The Encodable Gamma coordinate is retained, and the SAME final fold receives
[raw packed payload, pair Context Gamma]. No selector is changed. -/
def canonicalObjectProgram (p : GlobalSourcePackage.Inputs) : Program 2 :=
  pairOf (leftOf (.projection 1))
    (.composition (foldN (OriginalLambdaTraversalSelection.finalData p))
      ![rightOf (.projection 1),pairOf (.projection 0) (leftOf (.projection 1))])

/-- Equality on EVERY natural input vector, separate from internal evidence. -/
def CalibrationLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ v : List.Vector Nat 2,
    evaluate (canonicalObjectProgram p) v =
      OriginalFinalObjectCoherence.canonicalObject p (v.get 0) (v.get 1)

/-- All recovered coordinates are bound to the actual input, output and
SAME final fold. In particular gamma is not a typesNumber encoding. -/
def Recovered (p : GlobalSourcePackage.Inputs) {alpha : Type}
    (context input out gamma raw parameter canonicalRaw : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing input gamma raw ⊓
    (graph2 InternalPairing.pairing parameter context gamma ⊓
      (foldGraph (OriginalLambdaTraversalSelection.finalData p) canonicalRaw raw parameter ⊓
        graph2 InternalPairing.pairing out gamma canonicalRaw))

/-- Independent exposure for arbitrary symbolic inputs and outputs, together
with reverse introduction through the actual pair/select/fold composition.
All extra runtime coordinates are supplied internally in the forward half. -/
def ExposureLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context input out : OTerm alpha) (psi : Formula alpha),
    Nonempty (Derivation body Delta (graph2 (canonicalObjectProgram p) out context input)) →
    (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ h ∈ Delta, h.relabel j ∈ Theta) →
      ∀ gamma raw parameter canonicalRaw : OTerm beta,
      Nonempty (Derivation body Theta
        (Recovered p (context.relabel j) (input.relabel j) (out.relabel j)
          gamma raw parameter canonicalRaw)) →
      Nonempty (Derivation body Theta (psi.relabel j))) →
    Nonempty (Derivation body Delta psi)) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context input out gamma raw parameter canonicalRaw : OTerm alpha),
    Nonempty (Derivation body Delta
      (Recovered p context input out gamma raw parameter canonicalRaw)) →
    Nonempty (Derivation body Delta (graph2 (canonicalObjectProgram p) out context input)))

/-- The only endpoint assumptions: an actual original Object pair, the
unchanged seven original Shape graphs, original source acceptance and window.
No shifted acceptance, output identity or canonical endpoint is assumed. -/
def Premise (guard : Program 1) (p : GlobalSourcePackage.Inputs) {alpha : Type}
    (input raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing input gamma raw ⊓
    (OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType ⊓
      (graph2 (OriginalFinalVariableCanonical.originalSourceValidity guard p) (numeral 1) raw parameter ⊓
        OriginalFinalVariableCanonical.originalWindowGraph p raw parameter))

/-- All-output rigidity of the actual original wrapper, both before shift
and at EVERY genuine shiftObjectRaw output. The added type is unrestricted. -/
def FixednessLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out shiftedOut input shiftedObject raw shifted variableCode shiftedVariable typ index
      parameter extendedParameter context gamma extendedGamma addedType : OTerm alpha),
  let K := canonicalObjectProgram (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((Premise guard p input raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType).imp
      (((graph2 K out context input).iff (equal out input)) ⊓
        ((graph2 shiftObjectRaw shiftedObject addedType input).imp
          ((graph2 K shiftedOut context shiftedObject).iff (equal shiftedOut shiftedObject))))))

/-- Actual Object shift, SAME-final wrapper, original Object erasure and
SAME-final wrapper form the chain. Its result agrees with the original wrapper
output. No payload surrogate is substituted for any Object operation. -/
def CancellationLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (shiftOut canonicalShift erased out originalOut input raw shifted variableCode shiftedVariable
      typ index parameter extendedParameter context gamma extendedGamma addedType : OTerm alpha),
  let K := canonicalObjectProgram (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((Premise guard p input raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType).imp
      ((graph2 shiftObjectRaw shiftOut addedType input ⊓
        (graph2 K canonicalShift context shiftOut ⊓
          (graph1 eraseObjectRaw erased canonicalShift ⊓
            (graph2 K out context erased ⊓ graph2 K originalOut context input)))).imp
        (equal out originalOut))))

/-- Independent internal rank-one equations and preservation at both actual
Object endpoints, for every rank output and every genuine Object shift. -/
def RankLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (rank out shiftedOut input shiftedObject raw shifted variableCode shiftedVariable typ index
      parameter extendedParameter context gamma extendedGamma addedType : OTerm alpha),
  let K := canonicalObjectProgram (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((Premise guard p input raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType).imp
      (((graph1 variableRankObjectRaw rank input).iff (equal rank (numeral 1))) ⊓
        ((graph2 shiftObjectRaw shiftedObject addedType input).imp
          (((graph1 variableRankObjectRaw rank shiftedObject).iff (equal rank (numeral 1))) ⊓
            ((graph2 K out context input ⊓ graph2 K shiftedOut context shiftedObject).imp
              (((graph1 variableRankObjectRaw rank out).iff (graph1 variableRankObjectRaw rank input)) ⊓
                ((graph1 variableRankObjectRaw rank shiftedOut).iff
                  (graph1 variableRankObjectRaw rank shiftedObject)))))))))

/-- One original tuple is selected before windows and runtime contexts.
Retain the COMPLETE preceding canonical and native Properties at that SAME
once-refined tuple, with all six new obligations. No internal I/C is claimed. -/
def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (guard : Program 1) : Prop :=
  OriginalFinalVariableCanonical.Properties n arity p guard ∧
  OriginalFinalVariableCanonical.NativeProperties n arity p guard ∧
  CalibrationLaw (OriginalVariableLeaves.refineInputs guard p) ∧
  ExposureLaw (OriginalVariableLeaves.refineInputs guard p) ∧
  FixednessLaw guard p ∧ CancellationLaw guard p ∧ RankLaw guard p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObject
