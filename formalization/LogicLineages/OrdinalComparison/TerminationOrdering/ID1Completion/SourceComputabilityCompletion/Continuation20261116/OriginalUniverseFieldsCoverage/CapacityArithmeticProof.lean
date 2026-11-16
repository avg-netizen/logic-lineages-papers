module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem unarySize (size childSize bound : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn size (suc childSize))))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc bound)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childSize (suc bound))) :=
  InternalSquareRootArithmeticSupportProof.strictTrans childSize (suc childSize) (suc bound)
    (InternalCoprimeMultipleBoundedProof.selfLtSucc childSize)
    (InternalOriginalPairingOrderArithmeticProof.strictTransport (suc childSize) (suc bound) size (suc bound)
      ⟨symm (Classical.choice he)⟩ ⟨refl _⟩ hs)

theorem unaryPositive (size childSize : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn size (suc childSize)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z size)) :=
  InternalOriginalPairingOrderArithmeticProof.strictTransport z size z (suc childSize)
    ⟨refl _⟩ he (OriginalTypedEnumerationDepthBound.ArithmeticProof.positiveSuccessor childSize)

theorem sameLabel (label childLabel labels : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn label childLabel)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc labels)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childLabel (suc labels))) :=
  InternalOriginalPairingOrderArithmeticProof.strictTransport childLabel (suc labels) label (suc labels)
    ⟨symm (Classical.choice he)⟩ ⟨refl _⟩ hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
