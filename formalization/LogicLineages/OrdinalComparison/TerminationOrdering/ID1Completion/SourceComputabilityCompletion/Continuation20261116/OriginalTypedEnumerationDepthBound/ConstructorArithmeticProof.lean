module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BoundTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalAdditionLawsProof (add)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unary (childSize childDepth size depth : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (eqn size (suc childSize))))
    (hd : Nonempty (Derivation body Delta (eqn depth (suc childDepth))))
    (hc : Nonempty (Derivation body Delta (argumentsBound childDepth childSize))) :
    Nonempty (Derivation body Delta
      (termBound depth size ⊓ InternalLessThan.strictLess z size)) :=
  andIntro (BoundTransportProof.termTransport depth size (suc childDepth) (suc childSize) hd hs
    (ArithmeticProof.unaryGrowth childDepth childSize hc))
    (strictTransport z size z (suc childSize) ⟨refl _⟩ hs (ArithmeticProof.positiveSuccessor childSize))

theorem binary (ls rs dl dr maximum size depth : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (eqn size (suc (add ls rs)))))
    (hd : Nonempty (Derivation body Delta (eqn depth (suc maximum))))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum dl dr)))
    (hl : Nonempty (Derivation body Delta (argumentsBound dl ls)))
    (hr : Nonempty (Derivation body Delta (argumentsBound dr rs))) :
    Nonempty (Derivation body Delta
      (termBound depth size ⊓ InternalLessThan.strictLess z size)) :=
  andIntro (BoundTransportProof.termTransport depth size (suc maximum) (suc (add ls rs)) hd hs
    (BinaryArithmeticProof.binaryGrowth dl dr ls rs maximum hl hr hm))
    (strictTransport z size z (suc (add ls rs)) ⟨refl _⟩ hs (ArithmeticProof.positiveSuccessor (add ls rs)))

theorem cons (ls rs dl dr maximum size depth : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (eqn size (add ls rs))))
    (hd : Nonempty (Derivation body Delta (eqn depth (suc maximum))))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum dl dr)))
    (hl : Nonempty (Derivation body Delta (termBound dl ls ⊓ InternalLessThan.strictLess z ls)))
    (hr : Nonempty (Derivation body Delta (argumentsBound dr rs))) :
    Nonempty (Derivation body Delta (argumentsBound depth size)) :=
  BoundTransportProof.argumentsTransport depth size (suc maximum) (add ls rs) hd hs
    (BinaryArithmeticProof.consGrowth dl dr ls rs maximum (andRight hl) (andLeft hl) hr hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
