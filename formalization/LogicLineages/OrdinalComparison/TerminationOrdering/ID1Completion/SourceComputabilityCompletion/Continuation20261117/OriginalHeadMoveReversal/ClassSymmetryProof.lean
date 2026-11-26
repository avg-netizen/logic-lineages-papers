module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ClassSymmetryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atValues (source target cs ct : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cs source)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass ct target))) :
    Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) target source)) := by
  obtain ⟨he⟩ := (OriginalHeadClass.InternalProof.internalEquivalence body alpha Delta source target cs ct hs ht).mp h
  exact (OriginalHeadClass.InternalProof.internalEquivalence body alpha Delta target source ct cs ht hs).mpr
    ⟨InternalTagArithmeticSupportProof.symm he⟩

theorem atSource (source target cs : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cs source))) :
    Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) target source)) := by
  apply programCases OriginalHeadClass.headClass (Fin.cons target Fin.elim0) _
  intro beta j Theta ct hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hjj := renameInto h j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hjj hsj
  exact atValues (source.relabel j) (target.relabel j) (cs.relabel j) ct hjj hsj hx

theorem symmetric (source target : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target))) :
    Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) target source)) := by
  apply programCases OriginalHeadClass.headClass (Fin.cons source Fin.elim0) _
  intro beta j Theta cs hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hjj := renameInto h j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hjj
  exact atSource (source.relabel j) (target.relabel j) cs hjj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ClassSymmetryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ClassSymmetryProof
