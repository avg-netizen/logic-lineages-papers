module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.IntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderTransport (Accepted)
open OriginalUniverseDecoderTransportSyntaxProof (acceptedSubst acceptedRename)
open InternalStrongInduction
open Definitions InductionDefinitions

open BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atRawIntroFrom (H : Program 1) (M N W : Program 2) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (arguments : Bool) (typ gamma c : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (MemberIncluded M N c)) →
      Nonempty (Derivation body Theta (Accepted H M W arguments typ (raw.relabel j) gamma c)) →
      Nonempty (Derivation body Theta (Accepted H N W arguments typ (raw.relabel j) gamma c))) :
    Nonempty (Derivation body Delta (AtRaw H M N W raw)) := by
  let v : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  have one (arguments : Bool) : Nonempty (Derivation body
      (Delta.map (fun r => r.relabel Sum.inl))
      (Transport H M N W arguments (v 0) (raw.relabel Sum.inl) (v 1) (v 2))) := by
    let I := MemberIncluded M N (v 2)
    let A := Accepted H M W arguments (v 0) (raw.relabel Sum.inl) (v 1) (v 2)
    let Theta := A :: I :: Delta.map (fun r => r.relabel Sum.inl)
    obtain ⟨out⟩ := step (alpha ⊕ Fin 3) Sum.inl Theta arguments (v 0) (v 1) (v 2)
      (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩)))
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩
  obtain ⟨ht⟩ := one false
  obtain ⟨ha⟩ := one true
  exact atRawIntro H M N W raw ⟨Derivation.conjunctionIntroduction ht ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.IntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.IntroductionProof
