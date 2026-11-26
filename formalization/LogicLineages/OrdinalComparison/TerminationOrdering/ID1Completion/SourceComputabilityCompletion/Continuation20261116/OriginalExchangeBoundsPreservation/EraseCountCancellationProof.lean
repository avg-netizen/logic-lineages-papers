module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCountCancellationAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCountCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open EraseInvariantSyntaxProof
open Continuation20261114
open Continuation20261115.OriginalArgumentPermutationClosure
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof

theorem atQuery (left head tail right rest needle tc rc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (he : Nonempty (Derivation body Delta (EraseInvariant.countEffect right head rest (suc z))))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest needle))) :
    Nonempty (Derivation body Delta (eqn tc rc)) := by
  apply InternalAcceptanceSupportProof.programCases ArgumentEntryCount.count ![right,needle] _
  intro beta j Theta whole hj hw
  have hx : (fun i => (![right,needle] i).relabel j) = ![right.relabel j,needle.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hw
  rw [eqnRelabel]
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have hej := renameInto he j Theta hj
  have htj := renameInto ht j Theta hj
  have hrj := renameInto hr j Theta hj
  rw [graph2Rename] at hcj htj hrj
  rw [agreementRename] at haj
  simp only [countEffectRename,sucRelabel,zRelabel] at hej
  exact EraseCountCancellationAtProof.atCounts (left.relabel j) (head.relabel j) (tail.relabel j)
    (right.relabel j) (rest.relabel j) (needle.relabel j) (tc.relabel j) (rc.relabel j) whole
    hcj haj hej htj hrj hw

theorem cancel (left head tail right rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (he : Nonempty (Derivation body Delta (EraseInvariant.countEffect right head rest (suc z)))) :
    Nonempty (Derivation body Delta (agreement tail rest)) := by
  apply agreementIntro tail rest
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let query : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let tc : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields (tail.relabel j) (rest.relabel j) query tc rc :: Delta.map (fun q => q.relabel j)
  change Derivation body Theta (eqn tc rc)
  have hf : Nonempty (Derivation body Theta (fields (tail.relabel j) (rest.relabel j) query tc rc)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hcj
  rw [agreementRename] at haj
  simp only [countEffectRename,sucRelabel,zRelabel] at hej
  exact Classical.choice (atQuery (left.relabel j) (head.relabel j) (tail.relabel j)
    (right.relabel j) (rest.relabel j) query tc rc hcj haj hej (andLeft hf) (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCountCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCountCancellationProof
