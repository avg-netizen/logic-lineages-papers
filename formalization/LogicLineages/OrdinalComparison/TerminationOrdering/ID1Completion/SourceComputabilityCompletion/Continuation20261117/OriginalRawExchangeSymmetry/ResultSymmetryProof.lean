module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ResultSymmetryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem factor (source target cs ct : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult cs source)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult ct target))) :
    Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) source target)) ↔
    Nonempty (Derivation body Delta (eqn cs ct)) := by
  let l : Program 2 := .composition OriginalHeadResult.headResult (fun _ : Fin 1 => .projection 0)
  let r : Program 2 := .composition OriginalHeadResult.headResult (fun _ : Fin 1 => .projection 1)
  let xs : Fin 2 → OTerm alpha := ![source,target]
  have hl := unaryValue OriginalHeadResult.headResult (.projection 0) cs source xs hs (projectionValue 0 xs)
  have hr := unaryValue OriginalHeadResult.headResult (.projection 1) ct target xs ht (projectionValue 1 xs)
  constructor
  · intro h
    exact InternalEqualityTestProof.equalityOfAcceptance cs ct
      (binaryRecover InternalEqualityTest.equalityTest l r (numeral 1) cs ct xs h hl hr)
  · intro h
    exact binaryValue InternalEqualityTest.equalityTest l r (numeral 1) cs ct xs
      (InternalEqualityTestCompositionProof.equalityOfEqual cs ct h) hl hr

theorem atValues (source target cs ct : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) source target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult cs source)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult ct target))) :
    Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) target source)) := by
  obtain ⟨he⟩ := (factor source target cs ct hs ht).mp h
  exact (factor target source ct cs ht hs).mpr
    ⟨InternalTagArithmeticSupportProof.symm he⟩

theorem atSource (source target cs : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) source target)))
    (hs : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult cs source))) :
    Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) target source)) := by
  apply programCases OriginalHeadResult.headResult (Fin.cons target Fin.elim0) _
  intro beta j Theta ct hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hjj := renameInto h j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hjj hsj
  exact atValues (source.relabel j) (target.relabel j) (cs.relabel j) ct hjj hsj hx

theorem symmetric (source target : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) source target))) :
    Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (numeral 1) target source)) := by
  apply programCases OriginalHeadResult.headResult (Fin.cons source Fin.elim0) _
  intro beta j Theta cs hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hjj := renameInto h j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hjj
  exact atSource (source.relabel j) (target.relabel j) cs hjj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ResultSymmetryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ResultSymmetryProof
