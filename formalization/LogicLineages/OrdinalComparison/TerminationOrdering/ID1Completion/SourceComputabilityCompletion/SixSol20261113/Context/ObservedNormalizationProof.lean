module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion ObservedNormalizationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualAccepted : ActualAccepted := by
  intro p H G W P body alpha Delta out input typ parameter
  let A := premises p H G W P out input typ parameter
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  let q := Erasure.ObservedPut.prepared p H G W
  have hd := ObservedClassCoreProof.domains q H G W P out input typ parameter ha
  have ho := ObservedClassCoreProof.acceptedAt q H G W P out input typ parameter ha
  have ht := ObservedBoundedProof.allTests q H G W P out input typ parameter ha
  have hn := OriginalAllPositionAcceptedProof.acceptedIntro
    (preminimum p H G W) H G W P input out parameter (andLeft hd) ho ht
  obtain ⟨answer⟩ := andIntro (andLeft hd) (andIntro (andRight hd) hn)
  exact ⟨Derivation.implicationIntroduction answer⟩

theorem actualMinimum : ActualMinimum := by
  intro p H G W P body alpha Delta out input typ parameter inputMinimum outputMinimum
  let R := (OriginalClassContextAllPositionSelection.inputs (preminimum p H G W) H G W P).base.oldRepresentative
  let A := premises p H G W P out input typ parameter ⊓
    (graph2 R inputMinimum input parameter ⊓ graph2 R outputMinimum out parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨accept⟩ := actualAccepted p H G W P body alpha (A :: Delta) out input typ parameter
  obtain ⟨hp⟩ := andLeft ha
  have hc := Nonempty.intro (Derivation.implicationElimination accept hp)
  obtain ⟨law⟩ := OriginalAllPositionMinimumStatementChecks.actualMinimumCoherence
    (preminimum p H G W) H G W P body alpha (A :: Delta) input out inputMinimum outputMinimum parameter
  obtain ⟨args⟩ := andIntro (andLeft hc) (andIntro (andRight (andRight hc)) (andRight ha))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination law args)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationProof
