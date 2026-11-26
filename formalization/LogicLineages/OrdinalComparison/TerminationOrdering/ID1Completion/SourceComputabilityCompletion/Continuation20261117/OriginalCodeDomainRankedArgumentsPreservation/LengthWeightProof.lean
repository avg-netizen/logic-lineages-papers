module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LengthWeight LengthWeightSyntaxProof LengthWeightBindingProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalTagArithmeticSyntaxProof (eqn)
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let x : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
  let f := LengthWeight.fields (raw.relabel Sum.inl) (x 0) (x 1)
  let Theta : List (Formula (alpha ⊕ Fin 2)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 2) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := LengthWeightCoreProof.atRaw (raw.relabel Sum.inl) (x 0) (x 1)
    (andLeft hf) (andRight hf) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw raw)) :=
  rawInduction raw (fun _ _ r ih => step r ih)

theorem weightedFromLength (raw count out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out count InternalTagArithmeticSyntaxProof.z))) :
    Nonempty (Derivation body Delta (result raw out)) :=
  atRawApply raw count out (allRaw raw) (andIntro hl hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightProof
