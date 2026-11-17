module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseInvariantBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open EraseInvariant EraseInvariantSyntaxProof
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applyAt (raw needle rest bit query lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (countEffect raw needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc raw query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc bit))) ⊓
        ((eqn needle query).not.imp (eqn lc rc)))) := by
  unfold countEffect at h
  obtain ⟨d⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta _
    (fun i => emb (![query,lc,rc] i)) h
  rw [countEffectWitness] at d
  obtain ⟨hf⟩ := andIntro hl hr
  exact ⟨Derivation.implicationElimination d hf⟩

theorem equalQuery (raw needle rest bit query lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (countEffect raw needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc raw query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query)))
    (he : Nonempty (Derivation body Delta (eqn needle query))) :
    Nonempty (Derivation body Delta (eqn lc (OrdinaryArithmetic.addTerm rc bit))) := by
  obtain ⟨d⟩ := andLeft (applyAt raw needle rest bit query lc rc h hl hr)
  obtain ⟨he⟩ := he
  exact ⟨Derivation.implicationElimination d he⟩

theorem unequalQuery (raw needle rest bit query lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (countEffect raw needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc raw query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query)))
    (he : Nonempty (Derivation body Delta (eqn needle query).not)) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  obtain ⟨d⟩ := andRight (applyAt raw needle rest bit query lc rc h hl hr)
  obtain ⟨he⟩ := he
  exact ⟨Derivation.implicationElimination d he⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectBindingProof
