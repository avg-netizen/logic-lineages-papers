module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open OriginalActiveObservedMinimumTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The accepted active guard-collapse derivation recovers the actual
preguard minimum graph. Its independently checked least-hit law then applies
to that very output, without changing the class test, seed or parameter. -/
theorem actualOriginalActiveObservedMinimumInternalMinimum :
    ActualOriginalActiveObservedMinimumInternalMinimum := by
  intro p H G W P positive alpha Delta out seed parameter earlier
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P
  let q := OriginalActiveObservedClass.inputs p H G W P
  let A := graph2 T InternalOriginalStepGuard.one seed parameter ⊓
    (graph2 (OriginalActiveObservedClass.activation p H G W)
      InternalOriginalStepGuard.one seed parameter ⊓
      graph2 q.base.oldRepresentative out seed parameter)
  have ha : Derivation positive (A :: Delta) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨hcollapse⟩ :=
    OriginalActiveObservedClassCompletionProof.actualOriginalActiveObservedGuardCollapse
      p H G W P positive alpha (A :: Delta) seed out parameter
  have hminimum := Derivation.implicationElimination hcollapse ha
  obtain ⟨hlaw⟩ :=
    OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalMinimum
      T Q positive alpha (A :: Delta) out seed parameter earlier
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hlaw
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft ha) hminimum))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
