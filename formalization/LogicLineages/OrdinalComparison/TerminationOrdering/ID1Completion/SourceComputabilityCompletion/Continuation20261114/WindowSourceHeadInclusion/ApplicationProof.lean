module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem proof : Targets.InternalApplication := by
  intro n arity body alpha Delta raw payload sigma tau symbols types hp hpair hw
  apply programCases OriginalSourceHeads.rawWindow (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta out hj hr
  simp only [consTermRename,emptyRename] at hr
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hpairj := renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hpairj
  have hwj := renameInto hw j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hf := (HeadWindowBranchAdequacy.ApplicationProof.application n arity body beta Theta (raw.relabel j) (payload.relabel j) (sigma.relabel j) (tau.relabel j) (symbols.relabel j) (types.relabel j) hpj hpairj).mp hwj
  exact SupportProof.sourceFromRaw n arity out (raw.relabel j) (symbols.relabel j) (types.relabel j) hr hwj
    (RawHeadWindowCoverage.ApplicationProof.application body beta Theta (symbols.relabel j) (types.relabel j) out (raw.relabel j) (payload.relabel j) (sigma.relabel j) (tau.relabel j) hr hpairj hpj (andRight (andRight hf)) (andLeft hf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ApplicationProof
