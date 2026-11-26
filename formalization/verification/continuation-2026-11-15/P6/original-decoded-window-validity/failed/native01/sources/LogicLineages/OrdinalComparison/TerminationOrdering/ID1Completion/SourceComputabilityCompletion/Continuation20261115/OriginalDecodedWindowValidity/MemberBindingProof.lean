module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open Targets SyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalControlGraph
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
theorem membersIntro (n : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (memberMatrix n raw))) :
    Nonempty (Derivation body Delta (boundedMembers n raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 1 Delta _ h

theorem membersApply (n : Nat) (raw key : OTerm alpha)
    (h : Nonempty (Derivation body Delta (boundedMembers n raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw key))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess key (numeral n))) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 1 Delta
    (memberMatrix n raw) (fun _ => emb key) h
  rw [memberWitness] at h
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.MemberBindingProof
