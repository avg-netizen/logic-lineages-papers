module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountRemoveAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceResultProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EraseAbsence EraseAbsenceSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb bindEmbedding liftBind varBind)
open InternalTagArithmeticSupportProof (refl sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBinderTransportProof InternalTermSubstitutionProof
open Continuation20261114

theorem zero (raw needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count z raw needle))) :
    Nonempty (Derivation body Delta (result raw needle z)) := by
  obtain ⟨h⟩ := withHyp h (eqn (z : OTerm alpha) z)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem one (raw needle : OTerm alpha) :
    Nonempty (Derivation body Delta (result raw needle (suc z))) := by
  have bad : Derivation body (eqn (suc (z : OTerm alpha)) z :: Delta) (eqn (suc z) z) :=
    Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad))⟩

theorem zeroCount (raw needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (result raw needle z))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count z raw needle)) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination h (refl z)⟩

theorem bitTransport (raw needle bit other : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn bit other)))
    (h : Nonempty (Derivation body Delta (result raw needle bit))) :
    Nonempty (Derivation body Delta (result raw needle other)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (result (raw.relabel Sum.inl) (needle.relabel Sum.inl) (.var (.inr 0)))
    (emb bit) (emb other) he
  simp only [instantiate,bindEmbedding,resultSubst,liftBind,varBind] at d
  exact ⟨d h⟩

theorem rawTransport (raw other needle bit : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw other)))
    (h : Nonempty (Derivation body Delta (result raw needle bit))) :
    Nonempty (Derivation body Delta (result other needle bit)) := by
  obtain ⟨he⟩ := he
  obtain ⟨h⟩ := h
  have d := Derivation.equalityElimination
    (result (.var (.inr 0)) (needle.relabel Sum.inl) (bit.relabel Sum.inl))
    (emb raw) (emb other) he
  simp only [instantiate,bindEmbedding,resultSubst,liftBind,varBind] at d
  exact ⟨d h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceResultProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseAbsenceResultProof
