module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumIdempotenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSupportProof (symm)
open OriginalActiveClassKernel (Domain)
open OriginalActiveKernelMinimum OriginalActiveKernelMinimumTargets
open OriginalActiveKernelMinimumSupportProof OriginalActiveKernelMinimumCoherenceProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Internal Program totality supplies the second computation. Coherence
identifies its output with the original minimum; equality transports the
actual graph, so no second-run witness or fixedness premise is assumed. -/
theorem idempotentAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter : OTerm alpha)
    (hd : Nonempty (Derivation positive Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation positive Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out out parameter)) := by
  let R := (inputs p H G W P).base.oldRepresentative
  apply programCases R (Fin.cons out (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hv
  rw [graph2Rename]
  have hd' := renameInto hd j Theta hj
  rw [domainRename] at hd'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  have hs : Nonempty (Derivation positive Theta
      (graph2 R value (out.relabel j) (parameter.relabel j))) := by
    simpa only [consTermRename,emptyRename] using hv
  have hhit := minimumHit p H G W P (seed.relabel j) (out.relabel j)
    (parameter.relabel j) hd' hr'
  obtain ⟨he⟩ := coherenceAt p H G W P (seed.relabel j) (out.relabel j)
    (out.relabel j) value (parameter.relabel j) hd' hhit hr' hs
  rw [equal,InternalSourceInversionSupportProof.onEquality] at he
  exact outputTransport R value (out.relabel j)
    (Fin.cons (out.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    ⟨symm he⟩ hs

theorem actualOriginalActiveKernelMinimumIdempotence :
    ActualOriginalActiveKernelMinimumIdempotence := by
  intro p H G W P positive alpha Delta seed out parameter
  let A := Domain p H G W seed parameter ⊓
    graph2 (inputs p H G W P).base.oldRepresentative out seed parameter
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := idempotentAt p H G W P seed out parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hi⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumIdempotenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumIdempotenceProof
