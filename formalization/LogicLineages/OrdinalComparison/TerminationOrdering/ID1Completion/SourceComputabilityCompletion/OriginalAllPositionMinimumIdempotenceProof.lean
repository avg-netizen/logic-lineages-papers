module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIdempotenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSupportProof (symm)
open OriginalActiveClassKernel (Domain)
open OriginalAllPositionMinimumCoherenceTargets
open OriginalClassContextAllPositionSelection (inputs)
open OriginalAllPositionMinimumSupportProof
open OriginalActiveKernelMinimumSupportProof (domainRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Internal Program totality supplies the second computation. Coherence
identifies its output with the original minimum; equality transports the
actual graph, so no second-run witness or fixedness premise is assumed. -/
theorem idempotentAt (coherence : MinimumCoherence) (p : GlobalSourcePackage.Inputs) (H G : Program 1)
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
  obtain ⟨hcoherence⟩ := coherence p H G W P positive beta Theta
    (seed.relabel j) (out.relabel j) (out.relabel j) value (parameter.relabel j)
  obtain ⟨hinputs⟩ := andIntro hd' (andIntro hhit (andIntro hr' hs))
  have he := Derivation.implicationElimination hcoherence hinputs
  rw [equal,InternalSourceInversionSupportProof.onEquality] at he
  exact outputTransport R value (out.relabel j)
    (Fin.cons (out.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    ⟨symm he⟩ hs

theorem idempotenceFrom (coherence : MinimumCoherence) : MinimumIdempotence := by
  intro p H G W P positive alpha Delta seed out parameter
  let A := Domain p H G W seed parameter ⊓
    graph2 (inputs p H G W P).base.oldRepresentative out seed parameter
  have h : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := idempotentAt coherence p H G W P seed out parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hi⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIdempotenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIdempotenceProof
