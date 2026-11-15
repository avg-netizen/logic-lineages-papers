module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open CountAgreement CountAgreementSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalControlGraph
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
theorem agreementIntro (left right : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix left right))) :
    Nonempty (Derivation body Delta (agreement left right)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 3 Delta _ h

theorem agreementApply (left right needle lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (matrix left right) (fun i => emb (![needle,lc,rc] i)) h
  rw [matrixWitness] at h
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hl hr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
