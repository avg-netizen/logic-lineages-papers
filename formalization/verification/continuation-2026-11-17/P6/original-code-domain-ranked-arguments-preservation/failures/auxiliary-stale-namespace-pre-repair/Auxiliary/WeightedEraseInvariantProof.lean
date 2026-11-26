module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseInvariantProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open WeightedErase WeightedEraseSyntaxProof WeightedEraseBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (weight : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw weight raw))) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) := by
  apply atRawIntro weight raw
  let x : Fin 7 → OTerm (alpha ⊕ Fin 7) := fun i => .var (.inr i)
  let f := fields weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  let Theta : List (Formula (alpha ⊕ Fin 7)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 7) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := WeightedEraseCoreProof.atRaw weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
    (andLeft (andLeft hf)) (andRight (andLeft hf)) (andLeft (andRight hf))
    (andLeft (andRight (andRight hf))) (andRight (andRight (andRight hf))) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) :=
  rawInduction weight raw (fun _ _ r ih => step weight r ih)

theorem actualResult (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total raw)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingWeight rest)))
    (hw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle))) :
    Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight)) :=
  atRawApply weight raw needle acc bit rest total remainingWeight needleWeight (allRaw weight raw)
    (andIntro (andIntro hv hp) (andIntro ht (andIntro hr hw)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseInvariantProof
