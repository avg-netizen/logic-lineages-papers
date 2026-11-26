module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationCertificateConstructorsSupportProof
theorem step (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) := by
  apply atRawIntro n arity raw
  let x : Fin 6 → OTerm (alpha ⊕ Fin 6) := fun i => .var (.inr i)
  let f := fields n arity (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  let Theta : List (Formula (alpha ⊕ Fin 6)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 6) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := StepProof.reversed n arity (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (ofFields hf) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  rawInduction n arity raw (fun _ _ r ih => step n arity r ih)

theorem symmetry : Targets.InternalSymmetry := by
  intro n arity body alpha Delta source target node reverseNode window symbols types hp hr hw hs ht hc he
  exact atRawApply n arity source target node reverseNode window symbols types (allRaw n arity source)
    (Facts.toFields ⟨hp,hr,hw,hs,ht,hc,he⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Proof
