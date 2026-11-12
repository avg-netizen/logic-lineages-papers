module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalClassContextAllPositionObserver (deleteAt)
open InternalListCodecSupportProof (consGraph)
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteConsProof
open OriginalAllPositionContextDeleteDropProof
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalContextTwoDeletionCoreProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraphRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)

theorem consDeletionAt (gamma head tail deleted cutoff tailDeleted : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted (suc cutoff) gamma)))
    (ht : Nonempty (Derivation body Delta (graph2 deleteAt tailDeleted cutoff tail))) :
    Nonempty (Derivation body Delta (consGraph deleted head tailDeleted)) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons tailDeleted Fin.elim0)) _
  intro beta rho Theta actual hrho hactual
  rw [consGraphRename]
  have hc' := renameInto hc rho Theta hrho
  have hd' := renameInto hd rho Theta hrho
  have ht' := renameInto ht rho Theta hrho
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc' hd' ht'
  simp only [consTermRename,emptyRename] at hactual
  have hdel := iffBackward (deleteConsIff (gamma.relabel rho) (head.relabel rho) (tail.relabel rho)
    (cutoff.relabel rho) actual (tailDeleted.relabel rho) hc' hactual) ht'
  have he := valueUnique deleteAt actual (deleted.relabel rho)
    (Fin.cons (suc (cutoff.relabel rho)) (Fin.cons (gamma.relabel rho) Fin.elim0)) hdel hd'
  exact outputTransport InternalListCodec.consCode actual (deleted.relabel rho)
    (Fin.cons (head.relabel rho) (Fin.cons (tailDeleted.relabel rho) Fin.elim0)) he hactual

/-- All tail coordinates are actual program queries, not supplied oracles. -/
theorem consDeletionCases (gamma head tail deleted cutoff : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 deleteAt deleted (suc cutoff) gamma)))
    (step : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (tailDeleted : OTerm beta),
      (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (deleted.relabel rho) (head.relabel rho) tailDeleted)) →
      Nonempty (Derivation body Theta (graph2 deleteAt tailDeleted (cutoff.relabel rho) (tail.relabel rho))) →
      Nonempty (Derivation body Theta (psi.relabel rho))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases deleteAt (Fin.cons cutoff (Fin.cons tail Fin.elim0)) _
  intro beta rho Theta tailDeleted hrho ht
  have hc' := renameInto hc rho Theta hrho
  have hd' := renameInto hd rho Theta hrho
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc' hd'
  simp only [consTermRename,emptyRename] at ht
  exact step beta rho Theta tailDeleted hrho
    (consDeletionAt (gamma.relabel rho) (head.relabel rho) (tail.relabel rho)
      (deleted.relabel rho) (cutoff.relabel rho) tailDeleted hc' hd' ht) ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionQueryProof
