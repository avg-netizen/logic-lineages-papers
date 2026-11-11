module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSyntaxProof OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalNodeProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Bounded validator acceptance rules out rejection at the first visit.
The raw payload graph is used solely to expose the original successor fuel. -/
theorem acceptedInitialNode (s t m : Program 2) (state raw parameter payload : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) raw parameter)))
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)) := by
  let P := graph1 (nodeCheck s t m) (numeral 1) state
  have hn : Nonempty (Derivation body (P.not :: Gamma) P.not) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr := rejectedInitialRun s t m state raw parameter payload
    (weakenProof hi (fun q hq => List.mem_cons_of_mem P.not hq))
    (weakenProof hp (fun q hq => List.mem_cons_of_mem P.not hq)) hn
  have hf := unaryRecover finished (run s t m) (numeral 1) z
    (Fin.cons raw (Fin.cons parameter Fin.elim0))
    (weakenProof hv (fun q hq => List.mem_cons_of_mem P.not hq)) hr
  obtain ⟨hfalse⟩ := finishedFailureImpossible hf
  exact ⟨Derivation.classical hfalse⟩

/-- Initial-state and payload witnesses come from original Program totality
and are eliminated internally. The unchanged node theorem then recovers
the root oldSource/oldTarget and conditional original membership factors. -/
theorem acceptanceFactors (s t m : Program 2) (raw parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validator s t m) (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  let payload : Program 2 := rightOf (.projection 0)
  let qs : Fin 2 → Program 2 := ![initial,payload]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Delta hj hq
  rw [factorsRename]
  have hv' := renameInto hv j Delta hj
  simp only [graph2Rename,oneRename] at hv'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0)
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 1)
    (raw.relabel j) xx (hq 1) (projectionValue 0 xx)
  have hn := acceptedInitialNode s t m (ys 0) (raw.relabel j) (parameter.relabel j)
    (ys 1) hv' (hq 0) hp
  have hs := initialSelectors (ys 0) (raw.relabel j) (parameter.relabel j) (hq 0)
  exact recoverFactors s t m (ys 0) (raw.relabel j) (parameter.relabel j)
    (andLeft hs) (andRight hs) hn

theorem actualOriginalHereditaryInternalAcceptanceNode :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalAcceptanceNode := by
  intro body s t m alpha raw parameter
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  obtain ⟨h⟩ := acceptanceFactors (body := body) (Gamma := [A]) s t m raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
