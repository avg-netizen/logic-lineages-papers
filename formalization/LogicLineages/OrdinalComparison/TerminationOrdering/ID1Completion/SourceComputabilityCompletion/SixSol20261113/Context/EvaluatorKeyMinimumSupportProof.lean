module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open EvaluatorKeyPut UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem minimumFacts (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter earlier : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (minimumInputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.atMost out seed ⊓
        (graph3 (relationTest p H G W P) (numeral 1) seed out parameter ⊓
          ((InternalLessThan.strictLess earlier out).imp
            (graph3 (relationTest p H G W P) (numeral 1) seed earlier parameter).not)))) := by
  obtain ⟨ht⟩ := andLeft hd
  obtain ⟨hr⟩ := hr
  obtain ⟨law⟩ := OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalMinimum
    (OriginalTypedDecoder.target H G) (classTest p H G W P)
    body alpha Delta out seed parameter earlier
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction ht hr)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyMinimumSupportProof
