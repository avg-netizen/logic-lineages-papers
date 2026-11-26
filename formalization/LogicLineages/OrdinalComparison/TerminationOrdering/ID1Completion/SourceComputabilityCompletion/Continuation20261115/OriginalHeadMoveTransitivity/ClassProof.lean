module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.ClassProof
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

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
theorem atValues (source middle target cs cm ct : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source middle)))
    (hbc : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) middle target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cs source)))
    (hm : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cm middle)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass ct target)))
    : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)) := by
  obtain ⟨he1⟩ := (OriginalHeadClass.InternalProof.internalEquivalence body alpha Delta source middle cs cm hs hm).mp hab
  obtain ⟨he2⟩ := (OriginalHeadClass.InternalProof.internalEquivalence body alpha Delta middle target cm ct hm ht).mp hbc
  exact (OriginalHeadClass.InternalProof.internalEquivalence body alpha Delta source target cs ct hs ht).mpr
    ⟨InternalTagArithmeticSupportProof.trans he1 he2⟩

theorem atMiddle (source middle target cs cm : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source middle)))
    (hbc : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) middle target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cs source)))
    (hm : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cm middle)))
    : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)) := by
  apply programCases OriginalHeadClass.headClass (Fin.cons target Fin.elim0) _
  intro beta j Theta ct hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have habj := renameInto hab j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at habj
  have hbcj := renameInto hbc j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hbcj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact atValues (source.relabel j) (middle.relabel j) (target.relabel j) (cs.relabel j) (cm.relabel j) ct habj hbcj hsj hmj hx

theorem atSource (source middle target cs : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source middle)))
    (hbc : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) middle target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadClass.headClass cs source)))
    : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)) := by
  apply programCases OriginalHeadClass.headClass (Fin.cons middle Fin.elim0) _
  intro beta j Theta cm hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have habj := renameInto hab j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at habj
  have hbcj := renameInto hbc j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hbcj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  exact atMiddle (source.relabel j) (middle.relabel j) (target.relabel j) (cs.relabel j) cm habj hbcj hsj hx

theorem transitive (source middle target : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source middle)))
    (hbc : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) middle target)))
    : Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) source target)) := by
  apply programCases OriginalHeadClass.headClass (Fin.cons source Fin.elim0) _
  intro beta j Theta cs hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have habj := renameInto hab j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at habj
  have hbcj := renameInto hbc j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hbcj
  exact atSource (source.relabel j) (middle.relabel j) (target.relabel j) cs habj hbcj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.ClassProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadMoveTransitivity.ClassProof
