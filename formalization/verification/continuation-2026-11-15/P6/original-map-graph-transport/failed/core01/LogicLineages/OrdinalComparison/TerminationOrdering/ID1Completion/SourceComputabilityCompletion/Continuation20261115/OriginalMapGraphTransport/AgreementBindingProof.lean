module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Targets AgreementSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalControlGraph
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
theorem agreementIntro (keys left right : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (agreementMatrix keys left right))) :
    Nonempty (Derivation body Delta (lookupAgreement keys left right)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 2 Delta _ h

theorem agreementApply (keys left right key value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (lookupAgreement keys left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) keys key)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup value left key))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup value right key)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
    (agreementMatrix keys left right) (fun i => emb (![key,value] i)) h
  rw [matrixWitness] at h
  obtain ⟨hm⟩ := hm
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hm) hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementBindingProof
