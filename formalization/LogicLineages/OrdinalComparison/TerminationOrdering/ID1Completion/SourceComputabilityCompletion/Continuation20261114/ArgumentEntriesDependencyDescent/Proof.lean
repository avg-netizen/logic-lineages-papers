module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SupportProof
theorem childrenDescent (raw deps child : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) := by
  apply arityCases raw _
  · intro beta j Theta hj ha
    rw [strictRename]
    have hdj := renameInto hd j Theta hj
    have hmj := renameInto hm j Theta hj
    rw [graph1Rename] at hdj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    exact SupportProof.zeroCase (raw.relabel j) (deps.relabel j) (child.relabel j) ha hdj hmj
  · intro beta j Theta hj ha
    rw [strictRename]
    have hdj := renameInto hd j Theta hj
    have hmj := renameInto hm j Theta hj
    rw [graph1Rename] at hdj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    exact CasesProof.unary (raw.relabel j) (deps.relabel j) (child.relabel j) ha hdj hmj
  · intro beta j Theta hj ha
    rw [strictRename]
    have hdj := renameInto hd j Theta hj
    have hmj := renameInto hm j Theta hj
    rw [graph1Rename] at hdj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    exact CasesProof.binary (raw.relabel j) (deps.relabel j) (child.relabel j) ha hdj hmj

theorem dependencyDescent : Targets.InternalDependencyDescent := by
  intro body alpha Delta raw param deps child hd hm
  have hc := unaryRecover ArgumentEntriesChildren.children (.projection 0) deps raw
    (Fin.cons raw (Fin.cons param Fin.elim0)) hd
    (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0)))
  exact childrenDescent raw deps child hc hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
