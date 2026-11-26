module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.WindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
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

open InductionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)

theorem nonzeroOne (out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (BooleanValue out)))
    (hn : Nonempty (Derivation body Delta (eqn out (numeral 0)).not)) :
    Nonempty (Derivation body Delta (eqn out (numeral 1))) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hn⟩ := withHyp hn (eqn out (numeral 0))
  exact ⟨disjunctionElimination hr
    (Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

theorem atOutputs (n : Nat) (arity : Fin n → Nat) (raw symbols types pool value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow pool symbols types)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value raw symbols types)))
    (hs : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) := by
  have hq := (SourceHeadsFilterAdequacy.CompositionProof.internalSourceMember n arity body alpha Delta pool raw symbols types value hp hw).mp hs
  have he := nonzeroOne value (WindowProof.windowRange n arity body alpha Delta raw symbols types value hw) (andRight hq)
  exact outputTransport (OriginalHeadWindow.window n arity) value (numeral 1)
    (Fin.cons raw (Fin.cons symbols (Fin.cons types Fin.elim0))) he hw

theorem atPool (n : Nat) (arity : Fin n → Nat) (raw symbols types pool : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow pool symbols types)))
    (hs : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) := by
  apply programCases (OriginalHeadWindow.window n arity) (Fin.cons raw (Fin.cons symbols (Fin.cons types Fin.elim0))) _
  intro beta j Theta value hj hw
  simp only [consTermRename,emptyRename] at hw
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hpj hsj ⊢
  exact atOutputs n arity (raw.relabel j) (symbols.relabel j) (types.relabel j) (pool.relabel j) value hpj hw hsj

theorem sourceWindow : Targets.InternalSourceWindow := by
  intro n arity body alpha Delta raw symbols types hs
  apply programCases OriginalSourceHeads.rawWindow (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta pool hj hp
  simp only [consTermRename,emptyRename] at hp
  have hsj := renameInto hs j Theta hj
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hsj ⊢
  exact atPool n arity (raw.relabel j) (symbols.relabel j) (types.relabel j) pool hp hsj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.SourceProof
