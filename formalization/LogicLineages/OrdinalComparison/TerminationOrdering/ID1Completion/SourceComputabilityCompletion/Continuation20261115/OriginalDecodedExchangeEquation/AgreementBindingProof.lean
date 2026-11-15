module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open AgreementDefinitions AgreementSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (E : Program 2)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalControlGraph
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
theorem agreementIntro (keys left right : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (agreementMatrix E keys left right))) :
    Nonempty (Derivation body Delta (lookupAgreement E keys left right)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 2 Delta _ h

theorem agreementApply (keys left right key value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (lookupAgreement E keys left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) keys key)))
    (hl : Nonempty (Derivation body Delta (graph2 E value key left))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) right key)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
    (agreementMatrix E keys left right) (fun i => emb (![key,value] i)) h
  rw [matrixWitness E] at h
  obtain ⟨hm⟩ := hm
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hm) hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementBindingProof
