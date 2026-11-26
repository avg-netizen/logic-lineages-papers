module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Proof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open ExchangeInduction ExchangeInductionSyntaxProof ExchangeInductionBindingProof
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (n : Nat) (arity : Fin n → Nat)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) := by
  apply atRawIntro n arity raw
  let x : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  let f := fields n arity (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4)
  let Theta : List (Formula (alpha ⊕ Fin 5)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 5) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := ExchangeStepProof.preserved n arity (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4)
    (andLeft hf) (andLeft (andRight hf))
    (andLeft (andRight (andRight hf))) (andRight (andRight (andRight hf))) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  rawInduction n arity raw (fun _ _ r ih => step n arity r ih)

theorem preserved (node window left right lv rv : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (InternalTagArithmeticSyntaxProof.suc InternalTagArithmeticSyntaxProof.z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right))) :
    Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn lv rv)) :=
  atRawApply n arity left right node window lv rv (allRaw n arity left)
    (andIntro hp (andIntro he (andIntro hlv hrv)))

theorem rawExchangeVariableRank : Targets.InternalRawExchangeVariableRank := by
  intro n arity body alpha Delta left right node window leftRank rightRank hp _hl _hr he hleft hright
  exact preserved n arity node window left right leftRank rightRank hp he hleft hright

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Proof
