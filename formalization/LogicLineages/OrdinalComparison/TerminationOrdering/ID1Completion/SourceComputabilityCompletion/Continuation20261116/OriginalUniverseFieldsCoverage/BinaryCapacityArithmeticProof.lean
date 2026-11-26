module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryCapacityArithmeticProof
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

open InternalAdditionLawsProof (add)

theorem sizes (cons : Bool) (size leftSize rightSize bound : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn size (if cons then add leftSize rightSize else suc (add leftSize rightSize)))))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc bound)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess leftSize (suc bound) ⊓
      InternalLessThan.strictLess rightSize (suc bound))) := by
  have hsum : Nonempty (Derivation body Delta (InternalLessThan.strictLess (add leftSize rightSize) (suc bound))) := by
    cases cons
    · exact CapacityArithmeticProof.unarySize size (add leftSize rightSize) bound he hs
    · exact InternalOriginalPairingOrderArithmeticProof.strictTransport (add leftSize rightSize) (suc bound) size (suc bound)
        ⟨symm (Classical.choice he)⟩ ⟨refl _⟩ hs
  exact andIntro
    (InternalOriginalPairingOrderArithmeticProof.weakStrictTrans leftSize (add leftSize rightSize) (suc bound)
      (InternalUnpairArithmeticProof.leftWeakAdd leftSize rightSize) hsum)
    (InternalOriginalPairingOrderArithmeticProof.weakStrictTrans rightSize (add leftSize rightSize) (suc bound)
      (InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd leftSize rightSize) hsum)

theorem labels (label leftLabel rightLabel maximum bound : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn label maximum)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum leftLabel rightLabel)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc bound)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess leftLabel (suc bound) ⊓
      InternalLessThan.strictLess rightLabel (suc bound))) :=
  OriginalEnumerationMembership.MaximumProof.forward leftLabel rightLabel maximum bound hm
    (CapacityArithmeticProof.sameLabel label maximum bound he hl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryCapacityArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryCapacityArithmeticProof
