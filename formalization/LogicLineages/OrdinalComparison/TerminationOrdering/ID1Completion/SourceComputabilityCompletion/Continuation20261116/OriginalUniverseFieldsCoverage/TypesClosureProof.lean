module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
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
open InternalOriginalOrderSyntaxProof (addRelabel)
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem cons (raw typ tail allowed headSize tailSize : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw typ tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed typ)))
    (ha : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed tail allowed tailSize)))
    (hp : Nonempty (Derivation body Delta (InternalLessThan.strictLess z headSize))) :
    Nonempty (Derivation body Delta
      (OriginalEnumerationFields.Targets.typesAllowed raw allowed (add headSize tailSize))) := by
  apply InternalAcceptanceSupportProof.programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
  intro beta j Theta len hj hl
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hl
  rw [OriginalEnumerationFields.Types.AllowedSyntaxProof.allowedRename,addRelabel]
  have hcj := renameInto hc j Theta hj
  have hmj := renameInto hm j Theta hj
  have haj := renameInto ha j Theta hj
  have hpj := renameInto hp j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  rw [OriginalEnumerationFields.Types.AllowedSyntaxProof.allowedRename] at haj
  simp only [strictRename,zRelabel] at hpj
  exact TypesProof.consAtLength (raw.relabel j) (typ.relabel j) (tail.relabel j) (allowed.relabel j)
    (headSize.relabel j) (tailSize.relabel j) len hcj hmj haj hpj hl

theorem boundTransport (raw allowed actual known : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn actual known)))
    (ha : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed raw allowed known))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed raw allowed actual)) :=
  TypesProof.monotone raw allowed known actual ha
    (InternalOriginalPairingOrderArithmeticProof.strictTransport known (suc actual) actual (suc actual)
      ⟨symm (Classical.choice he)⟩ ⟨refl _⟩ (InternalCoprimeMultipleBoundedProof.selfLtSucc actual))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
