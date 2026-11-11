module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectWrapperSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalParameterizedCanonicalResultFold (foldN foldGraph)
open UniformCertificateCompletion OriginalFinalVariableObject
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Queries read the actual Object and the actual parameter fed to the fold. -/
def objectContext : Program 2 := leftOf (.projection 1)
def objectPayload : Program 2 := rightOf (.projection 1)
def objectParameter : Program 2 := pairOf (.projection 0) objectContext
def canonicalPayload (p : GlobalSourcePackage.Inputs) : Program 2 :=
  .composition (foldN (OriginalLambdaTraversalSelection.finalData p)) ![objectPayload,objectParameter]
def wrapperQueries (p : GlobalSourcePackage.Inputs) : Fin 4 → Program 2 :=
  ![objectContext,objectPayload,objectParameter,canonicalPayload p]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Expose every supplied query through original projection/unpair/pair/fold
rules. The input pair is reconstructed, rather than assumed in this lemma. -/
theorem recoveredAt (p : GlobalSourcePackage.Inputs) (context input out : OTerm alpha)
    (ys : Fin 4 → OTerm alpha)
    (hs : ∀ i, Nonempty (Derivation body Delta
      (programGraph (wrapperQueries p i) (ys i) (Fin.cons context (Fin.cons input Fin.elim0)))))
    (ho : Nonempty (Derivation body Delta (graph2 (canonicalObjectProgram p) out context input))) :
    Nonempty (Derivation body Delta (Recovered p context input out (ys 0) (ys 1) (ys 2) (ys 3))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons context (Fin.cons input Fin.elim0)
  have hl := unaryRecover InternalUnpair.left (.projection 1) (ys 0) input xs
    (hs 0) (projectionValue 1 xs)
  have hr := unaryRecover InternalUnpair.right (.projection 1) (ys 1) input xs
    (hs 1) (projectionValue 1 xs)
  have hp := reconstructPair input (ys 0) (ys 1) hl hr
  have hparam := binaryRecover InternalPairing.pairing (.projection 0) objectContext
    (ys 2) context (ys 0) xs (hs 2) (projectionValue 0 xs) (hs 0)
  have hf := binaryRecover (foldN (OriginalLambdaTraversalSelection.finalData p))
    objectPayload objectParameter (ys 3) (ys 1) (ys 2) xs (hs 3) (hs 1) (hs 2)
  have hout := binaryRecover InternalPairing.pairing objectContext (canonicalPayload p)
    out (ys 0) (ys 3) xs ho (hs 0) (hs 3)
  exact andIntro hp (andIntro hparam (andIntro hf hout))

/-- Reverse introduction evaluates exactly the frozen wrapper composition. -/
theorem wrapperBackward (p : GlobalSourcePackage.Inputs)
    (context input out gamma raw parameter canonicalRaw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
    (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
    (hf : Nonempty (Derivation body Delta
      (foldGraph (OriginalLambdaTraversalSelection.finalData p) canonicalRaw raw parameter)))
    (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out gamma canonicalRaw))) :
    Nonempty (Derivation body Delta (graph2 (canonicalObjectProgram p) out context input)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons context (Fin.cons input Fin.elim0)
  have hl := unaryValue InternalUnpair.left (.projection 1) gamma input xs
    (pairLeft input gamma raw hp) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) raw input xs
    (pairRight input gamma raw hp) (projectionValue 1 xs)
  have hparam' := binaryValue InternalPairing.pairing (.projection 0) objectContext
    parameter context gamma xs hparam (projectionValue 0 xs) hl
  have hf' := binaryValue (foldN (OriginalLambdaTraversalSelection.finalData p))
    objectPayload objectParameter canonicalRaw raw parameter xs hf hr hparam'
  exact binaryValue InternalPairing.pairing objectContext (canonicalPayload p)
    out gamma canonicalRaw xs hout hl hf'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectWrapperSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectWrapperSupportProof
