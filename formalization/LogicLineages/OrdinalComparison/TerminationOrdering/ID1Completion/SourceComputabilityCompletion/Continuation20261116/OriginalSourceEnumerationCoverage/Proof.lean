module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.AssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.QueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem internalTermEnumeration : Targets.InternalTermEnumeration := by
  intro n arity H body alpha Delta seed param context gamma types heads typ raw pair size maxLabel seedSize seedLabel out
    hcontext hgamma htypes hheads hseedSize hseedLabel hclosed ha hb hp hs hl hout
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (QueriesProof.queries n arity) ![seed,param] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![seed,param] i).relabel j) = ![seed.relabel j,param.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcontextj := renameInto hcontext j Theta hj
  have hgammaj := renameInto hgamma j Theta hj
  have htypesj := renameInto htypes j Theta hj
  have hheadsj := renameInto hheads j Theta hj
  have hseedSizej := renameInto hseedSize j Theta hj
  have hseedLabelj := renameInto hseedLabel j Theta hj
  have hclosedj := renameInto hclosed j Theta hj
  have haj := renameInto ha j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  have hlj := renameInto hl j Theta hj
  have houtj := renameInto hout j Theta hj
  simp only [graph1Rename,graph2Rename] at hcontextj hgammaj htypesj hheadsj hseedSizej hseedLabelj hbj hpj houtj
  rw [WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename] at hclosedj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at haj
  simp only [ArgumentEntriesDependencyDescent.SupportProof.strictRename,sucRelabel] at hsj hlj
  exact AssemblyProof.atValues n arity H (seed.relabel j) (param.relabel j) (context.relabel j) (gamma.relabel j)
    (types.relabel j) (heads.relabel j) (typ.relabel j) (raw.relabel j) (pair.relabel j) (size.relabel j)
    (maxLabel.relabel j) (seedSize.relabel j) (seedLabel.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    hcontextj hgammaj htypesj hheadsj hseedSizej hseedLabelj hclosedj haj hbj hpj hsj hlj houtj
    (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Proof
