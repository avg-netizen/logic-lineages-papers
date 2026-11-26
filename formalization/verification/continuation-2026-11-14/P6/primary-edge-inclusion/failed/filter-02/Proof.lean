module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrimaryExpansion

theorem expansionEdgeInclusion : Targets.ExpansionEdgeInclusion := by
  intro E body alpha Delta pool reached source candidate parameter out hm hp hedge he
  have hany := AnyProof.anyIntroduction E body alpha Delta reached source candidate parameter hm hedge
  let xs : Fin 3 → OTerm alpha := ![pool,reached,parameter]
  apply programCases (filterReached E) xs _
  intro beta j Theta filtered hj hf
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
  have hany' := renameInto hany j Theta hj
  simp only [graph3Rename,numeral,sucRelabel,zRelabel] at hany'
  let ys : Fin 3 → OTerm beta := ![pool.relabel j,reached.relabel j,parameter.relabel j]
  have hxs : (fun i => (xs i).relabel j) = ys := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  have hf' : Nonempty (Derivation body Theta (programGraph (filterReached E) filtered ys)) := by
    rw [hxs] at hf
    exact hf
  have hmember := FilterProof.filterIntroduction E body beta Theta (pool.relabel j)
    (reached.relabel j) (candidate.relabel j) (parameter.relabel j) filtered hp' hany' hf'
  have ha := binaryRecover append (.projection 1) (filterReached E) (out.relabel j)
    (reached.relabel j) filtered ys he' (projectionValue 1 ys) hf'
  exact AppendRightProof.appendRightMembership body beta Theta (reached.relabel j) filtered
    (out.relabel j) (candidate.relabel j) ha hmember
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Proof
