module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIdempotenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherMinimumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalActiveKernelMinimumSupportProof (domainRename)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem minimumHit (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (seed out parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 (minimumInputs p H G W P).base.oldRepresentative out seed parameter))) :
 Nonempty (Derivation body Delta (Domain p H G W out parameter ⊓ Same p H G W seed out parameter)) := by
 have hf := EvaluatorKeyMinimumSupportProof.minimumFacts p H G W P seed out parameter seed hd hr
 exact EvaluatorKeyPutInternalProof.actualHit p H G W P body alpha Delta seed out parameter hd (andLeft (andRight hf))
theorem idempotent (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (seed out parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 (minimumInputs p H G W P).base.oldRepresentative out seed parameter))) :
 Nonempty (Derivation body Delta (graph2 (minimumInputs p H G W P).base.oldRepresentative out out parameter)) := by
 let R := (minimumInputs p H G W P).base.oldRepresentative
 apply programCases R (Fin.cons out (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hv
 rw [graph2Rename]
 have hd' := renameInto hd j Theta hj
 rw [domainRename] at hd'
 have hr' := renameInto hr j Theta hj
 rw [graph2Rename] at hr'
 have hs : Nonempty (Derivation body Theta (graph2 R value (out.relabel j) (parameter.relabel j))) := by
   simpa only [consTermRename,emptyRename] using hv
 have hh := minimumHit p H G W P (seed.relabel j) (out.relabel j) (parameter.relabel j) hd' hr'
 have he := EvaluatorKeyMinimumProof.actualMinimumEquality p H G W P body beta Theta
   (seed.relabel j) (out.relabel j) (out.relabel j) value (parameter.relabel j)
   hd' (andLeft hh) (andRight hh) hr' hs
 have heq := (congrArg (fun f => Nonempty (Derivation body Theta f))
   (equalEqn (out.relabel j) value)).mp he
 obtain ⟨heq⟩ := heq
 exact outputTransport R value (out.relabel j)
   (Fin.cons (out.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) ⟨symm heq⟩ hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherMinimumProof
