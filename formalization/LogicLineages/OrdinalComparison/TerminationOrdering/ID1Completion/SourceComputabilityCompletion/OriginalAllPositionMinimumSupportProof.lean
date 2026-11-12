module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalActiveClassKernel (Domain)
open OriginalAllPositionMinimumCoherenceTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-side supplier awaiting the independently derived exact row law. -/
def HitDomain : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed other parameter : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta (Domain p H G W seed parameter)) →
  Nonempty (Derivation body Delta (Accepted p H G W P seed other parameter)) →
  Nonempty (Derivation body Delta (Domain p H G W other parameter))

theorem minimumFacts (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter earlier : InternalGraphComposition.OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.atMost out seed ⊓
        (Accepted p H G W P seed out parameter ⊓
          ((InternalLessThan.strictLess earlier out).imp (Accepted p H G W P seed earlier parameter).not)))) := by
  obtain ⟨hd⟩ := hd
  obtain ⟨hr⟩ := hr
  obtain ⟨hm⟩ := OriginalActiveObservedMinimumInternalProof.actualOriginalActiveObservedMinimumInternalMinimum
    p H G W (OriginalClassContextAllPositionSelection.classTest p H G W P)
    body alpha Delta out seed parameter earlier
  exact ⟨Derivation.implicationElimination hm
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hd)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight hd) hr))⟩

theorem minimumHit (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter : InternalGraphComposition.OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta (Accepted p H G W P seed out parameter)) :=
  andLeft (andRight (minimumFacts p H G W P seed out parameter seed hd hr))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumSupportProof
