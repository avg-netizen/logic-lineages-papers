module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.FilterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalOriginalUniformVertexPathSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem qualifiesRename {alpha beta : Type} (raw needle value : OTerm alpha) (j : alpha → beta) :
    (qualifies raw needle value).relabel j = qualifies (raw.relabel j) (needle.relabel j) (value.relabel j) := by
  simp only [qualifies,InternalRecursionGraphStepSyntaxProof.conjunctionRename,
    InductionSyntaxProof.notRename,graph2Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem internalSourceMember : Targets.InternalSourceMember := by
  intro n arity body alpha Delta raw needle symbols types value hr hw
  constructor
  · intro h
    apply programCases (OriginalSourceHeads.filterHeads n arity)
      (Fin.cons raw (Fin.cons symbols (Fin.cons types Fin.elim0))) _
    intro beta j Theta out hj hf
    simp only [consTermRename,emptyRename] at hf
    have hrj := renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hwj := renameInto hw j Theta hj
    rw [graph3Rename] at hwj
    have hh := renameInto h j Theta hj
    rw [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hh
    have hs : Nonempty (Derivation body Theta (graph2 (OriginalSourceHeads.sourceHeads n arity)
        out (symbols.relabel j) (types.relabel j))) := by
      exact ternaryValue (OriginalSourceHeads.filterHeads n arity) OriginalSourceHeads.rawWindow
        (.projection 0) (.projection 1) out (raw.relabel j) (symbols.relabel j) (types.relabel j)
        (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hf hrj
        (projectionValue 0 _) (projectionValue 1 _)
    let xs : Fin 3 → OTerm beta := Fin.cons (needle.relabel j) (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0))
    let query : Program 3 := .composition (OriginalSourceHeads.sourceHeads n arity) ![.projection 1,.projection 2]
    have hq : Nonempty (Derivation body Theta (programGraph query out xs)) :=
      binaryValue (OriginalSourceHeads.sourceHeads n arity) (.projection 1) (.projection 2) out
        (symbols.relabel j) (types.relabel j) xs hs (projectionValue 1 xs) (projectionValue 2 xs)
    have hiff := FilterProof.internalFilter n arity body beta Theta (raw.relabel j) out (needle.relabel j)
      (symbols.relabel j) (types.relabel j) (value.relabel j) hf hwj
    rw [qualifiesRename]
    exact hiff.mp (binaryRecover contains query (.projection 0) (numeral 1) out (needle.relabel j) xs hh hq (projectionValue 0 xs))
  · intro h
    apply programCases (OriginalSourceHeads.filterHeads n arity)
      (Fin.cons raw (Fin.cons symbols (Fin.cons types Fin.elim0))) _
    intro beta j Theta out hj hf
    simp only [consTermRename,emptyRename] at hf
    have hrj := renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hwj := renameInto hw j Theta hj
    rw [graph3Rename] at hwj
    have hh := renameInto h j Theta hj
    rw [qualifiesRename] at hh
    have hs : Nonempty (Derivation body Theta (graph2 (OriginalSourceHeads.sourceHeads n arity)
        out (symbols.relabel j) (types.relabel j))) := by
      exact ternaryValue (OriginalSourceHeads.filterHeads n arity) OriginalSourceHeads.rawWindow
        (.projection 0) (.projection 1) out (raw.relabel j) (symbols.relabel j) (types.relabel j)
        (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hf hrj
        (projectionValue 0 _) (projectionValue 1 _)
    let xs : Fin 3 → OTerm beta := Fin.cons (needle.relabel j) (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0))
    let query : Program 3 := .composition (OriginalSourceHeads.sourceHeads n arity) ![.projection 1,.projection 2]
    have hq : Nonempty (Derivation body Theta (programGraph query out xs)) :=
      binaryValue (OriginalSourceHeads.sourceHeads n arity) (.projection 1) (.projection 2) out
        (symbols.relabel j) (types.relabel j) xs hs (projectionValue 1 xs) (projectionValue 2 xs)
    have hiff := FilterProof.internalFilter n arity body beta Theta (raw.relabel j) out (needle.relabel j)
      (symbols.relabel j) (types.relabel j) (value.relabel j) hf hwj
    simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
    exact binaryValue contains query (.projection 0) (numeral 1) out (needle.relabel j) xs
      (hiff.mpr hh) hq (projectionValue 0 xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CompositionProof
