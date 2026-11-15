module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.ValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consEquation : Targets.InternalConsEquation := by
  intro body alpha Delta raw tau head tail param tailValue value hc ht
  constructor
  · intro he
    apply programCases ArgumentEntriesLayer.step ![raw,tailValue] _
    intro beta j Theta inner hj hi
    rw [graph2Rename]
    have hxs : (fun i : Fin 2 => ((![raw,tailValue] : Fin 2 → OTerm alpha) i).relabel j) =
        Fin.cons (raw.relabel j) (Fin.cons (tailValue.relabel j) Fin.elim0) := by
      funext i
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) i <;> rfl
    rw [hxs] at hi
    change Nonempty (Derivation body Theta (graph2 ArgumentEntriesLayer.step inner (raw.relabel j) (tailValue.relabel j))) at hi
    have hcj := renameInto hc j Theta hj
    rw [graph3Rename] at hcj
    have htj := renameInto ht j Theta hj
    rw [graph2Rename] at htj
    have hej := renameInto he j Theta hj
    rw [graph2Rename] at hej
    have hx := ValueProof.consValue (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j)
      (param.relabel j) (tailValue.relabel j) inner hcj htj hi
    have hq := valueUnique ArgumentEntriesRecursor.extract inner (value.relabel j) ![raw.relabel j,param.relabel j] hx hej
    exact outputTransport ArgumentEntriesLayer.step inner (value.relabel j) ![raw.relabel j,tailValue.relabel j] hq hi
  · exact ValueProof.consValue raw tau head tail param tailValue value hc ht

theorem consSuccess : Targets.InternalConsSuccess := by
  intro body alpha Delta raw tau head tail param tailEntries entry listCode hc ht hp hl
  exact (consEquation body alpha Delta raw tau head tail param (suc tailEntries) (suc listCode) hc ht).mpr
    (ArgumentEntriesLayer.InternalProof.internalConsSuccess body alpha Delta raw tau head tail tailEntries entry listCode hc hp hl)

theorem consFailure : Targets.InternalConsFailure := by
  intro body alpha Delta raw tau head tail param hc ht
  exact (consEquation body alpha Delta raw tau head tail param z z hc ht).mpr
    (ArgumentEntriesLayer.InternalProof.internalConsFailure body alpha Delta raw tau head tail hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Proof
