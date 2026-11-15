module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof InternalBinderTransportProof
open SplitInductionDefinitions SplitInductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atRawIntro (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 1 Delta _ h

theorem atRawApply (raw out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw raw)))
    (hf : Nonempty (Derivation body Delta (fields raw out))) :
    Nonempty (Derivation body Delta (result raw out)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 1 Delta
    (matrix raw) (fun _ => emb out) h
  rw [matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem induction (raw : OTerm alpha)
    (base : Nonempty (Derivation body Delta (AtRaw z)))
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (x : OTerm beta),
      Nonempty (Derivation body Theta (AtRaw x)) →
      Nonempty (Derivation body Theta (AtRaw (suc x)))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate
  have hb : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    rw [rawPredicateInstantiate]
    exact base
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    unfold theta rawPredicate successorInstance
    rw [nextEmbedding,atRawSubst]
    simp only [Term.subst,InternalAdditionLawsProof.varNext]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb raw) (natInduction theta hb hs)
  change Derivation body Delta (instantiate rawPredicate (emb raw)) at h
  rw [rawPredicateInstantiate] at h
  exact ⟨h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitBindingProof
