module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original typed wrappers: Encodable.encode Gamma stays distinct
from typesNumber Gamma. These standard-model equations do not imply any
symbolic internal graph fact. Erasure is actual single-bottom substitution. -/
def ActualRawObjectTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma tau : Ty),
  (∀ q : AuxTerm (Fin n) arity Gamma tau,
    evaluate shiftObjectRaw
      (List.Vector.ofFn ![typeNumber sigma,ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)]) =
    ContextUniform.objectCode (sigma :: Gamma)
      (packedNumber ⟨tau,rename q (NumberedAuxiliaryShift.prefixWeakening [] Gamma sigma)⟩)) ∧
  (∀ q : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
    evaluate eraseObjectRaw
      (List.Vector.ofFn ![ContextUniform.objectCode (sigma :: Gamma) (packedNumber ⟨tau,q⟩)]) =
    ContextUniform.objectCode Gamma
      (packedNumber ⟨tau,substitute q (singleSubstitution (.bottom sigma))⟩)) ∧
  (∀ q : AuxTerm (Fin n) arity Gamma tau,
    evaluate variableRankObjectRaw
      (List.Vector.ofFn ![ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)]) =
    NumberedVariableCount.variableCount q)

/-- Recover all context/payload witnesses internally from an arbitrary
symbolic shift graph. The input Object's pair shape is not an external premise.
Relabelled continuations retain the SAME positive body and logical hypotheses. -/
def ActualRawObjectInternalShiftExposure : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d input shifted : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ gamma packed extendedGamma shiftedPacked : OTerm beta,
    Nonempty (Derivation body Theta
      (ShiftRecovered (d.relabel j) (input.relabel j) (shifted.relabel j)
        gamma packed extendedGamma shiftedPacked)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- An actual context-cons witness is essential. No arbitrary raw context is
silently assumed to be nonempty, and no native decoding is an internal premise. -/
def ActualRawObjectInternalEraseExposure : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d input erased gamma packed extendedGamma : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalPairing.pairing input extendedGamma packed)) →
  Nonempty (Derivation body Delta
    (graph2 InternalListCodec.consCode extendedGamma d gamma)) →
  Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ erasedPacked : OTerm beta,
    Nonempty (Derivation body Theta
      (EraseRecovered (d.relabel j) (input.relabel j) (erased.relabel j)
        (gamma.relabel j) (packed.relabel j) (extendedGamma.relabel j) erasedPacked)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- ALL raw Object naturals, not just typed or canonical objects. The internal
half is independent of native calibration. This is raw bookkeeping cancellation
only, not cancellation across the final canonical fold or any C/I transport. -/
def ActualRawObjectCancellation : Prop :=
  (∀ d input : Nat,
    evaluate eraseObjectRaw
      (List.Vector.ofFn ![evaluate shiftObjectRaw (List.Vector.ofFn ![d,input])]) = input) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d input shifted erased : OTerm alpha),
    Nonempty (Derivation body Delta
      ((graph2 shiftObjectRaw shifted d input ⊓ graph1 eraseObjectRaw erased shifted).imp
        (equal erased input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportTargets
