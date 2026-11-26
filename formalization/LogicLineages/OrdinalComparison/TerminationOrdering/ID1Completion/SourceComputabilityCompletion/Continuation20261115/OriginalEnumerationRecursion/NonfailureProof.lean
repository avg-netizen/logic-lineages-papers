module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NonfailureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalEnumerationRecursionInterface
attribute [local irreducible] programGraph

theorem internalNonfailure : Targets.InternalNonfailure := by
  intro body alpha Delta n node answers param out ho
  let inner : Program 3 := InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n)
  apply InternalAcceptanceSupportProof.programCases inner ![node,answers,param] _
  intro beta j Theta value hj hv
  change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
  rw [eqnRelabel,zRelabel]
  have hxs : (fun i : Fin 3 => (![node,answers,param] i).relabel j) =
      ![node.relabel j,answers.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs] at hv
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  have hs : Nonempty (Derivation body Theta
      (graph3 (G n) (suc value) (node.relabel j) (answers.relabel j) (param.relabel j))) :=
    unaryValue .succ inner (suc value) value ![node.relabel j,answers.relabel j,param.relabel j]
      (successorValue (Fin.cons value Fin.elim0)) hv
  have he := valueUnique (G n) (out.relabel j) (suc value)
    ![node.relabel j,answers.relabel j,param.relabel j] hoj hs
  exact OriginalCodeBoundsCacheCoherence.DomainSupportProof.unequalZero (out.relabel j) value he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NonfailureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NonfailureProof
