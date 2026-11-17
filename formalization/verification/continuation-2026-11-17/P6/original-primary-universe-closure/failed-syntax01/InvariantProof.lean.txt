module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem eliminate (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw gamma context : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (allAccepted n arity reached gamma context)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached candidate)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ raw))) :
    Nonempty (Derivation body Delta (accepted n arity typ raw gamma context)) := by
  obtain ⟨h⟩ := elimination body alpha 3 Delta _ (fun i => emb (![candidate,typ,raw] i)) hi
  rw [memberWitness] at h
  obtain ⟨ha⟩ := andIntro hm hp
  exact ⟨Derivation.implicationElimination h ha⟩

theorem introduce (n : Nat) (arity : Fin n → Nat)
    (reached gamma context : OTerm alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (candidate typ raw : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 contains (numeral 1) (reached.relabel j) candidate)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate typ raw)) →
      Nonempty (Derivation body Theta
        (accepted n arity typ raw (gamma.relabel j) (context.relabel j)))) :
    Nonempty (Derivation body Delta (allAccepted n arity reached gamma context)) := by
  apply introduction body alpha 3 Delta
  let candidate : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let raw : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := graph2 contains (numeral 1) (reached.relabel Sum.inl) candidate ⊓
    graph2 InternalPairing.pairing candidate typ raw
  obtain ⟨h⟩ := next (alpha ⊕ Fin 3) Sum.inl
    (A :: Delta.map (fun q => q.relabel Sum.inl)) candidate typ raw
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
