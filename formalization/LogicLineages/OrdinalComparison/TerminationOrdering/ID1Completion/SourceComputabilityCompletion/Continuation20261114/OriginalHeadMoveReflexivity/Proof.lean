module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.ClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.BasicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.RankedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Proof
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

theorem accept (n : Nat) (arity : Fin n → Nat) (raw base list symbols types : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)))
    (hs : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.member n arity) (numeral 1) raw symbols types)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
      ![raw,base,raw,base,symbols,types])) :=
  (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta raw base raw base symbols types).mpr
    (andIntro (andIntro (andIntro hw hs) (ClassProof.classSelf body alpha Delta raw))
      (ArgumentPermutationReflexivity.Proof.original body alpha Delta base list he))

theorem basic : Targets.InternalBasic := by
  intro n arity body alpha Delta which raw base list symbols types hp hw he
  exact accept n arity raw base list symbols types hw
    (WindowSourceHeadInclusion.BasicProof.proof n arity body alpha Delta which raw symbols types hp hw) he

theorem unary : Targets.InternalUnary := by
  intro n arity body alpha Delta which raw payload base list symbols types hc hp hw he
  exact accept n arity raw base list symbols types hw
    (WindowSourceHeadInclusion.UnaryProof.proof n arity body alpha Delta which raw payload symbols types hc hp hw) he

theorem application : Targets.InternalApplication := by
  intro n arity body alpha Delta raw payload sigma tau base list symbols types hp hpair hw he
  exact accept n arity raw base list symbols types hw
    (WindowSourceHeadInclusion.ApplicationProof.proof n arity body alpha Delta raw payload sigma tau symbols types hp hpair hw) he

theorem ranked : Targets.InternalRanked := by
  intro n arity body alpha Delta raw symbol base list symbols types hp hw he
  exact accept n arity raw base list symbols types hw
    (WindowSourceHeadInclusion.RankedProof.proof n arity body alpha Delta raw symbol symbols types hp hw) he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Proof
