module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankLeftTapePositionProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (moveQuad)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceOpenIntroProof (exact_InstallOpenZeroRankOutput)
open NumberedWindowInternalParameterizedPositiveFold (iterateAt)
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
  (loopAt exact_OpenParameterizedLoopStep exact_OpenParameterizedLoopStart)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Finite genuine consecutive zero-rank rows. The held raw witnesses
are original advances at the exact encoded current, not host transitions. -/
inductive Rows (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (g : Program 1) (raw : Program 5) (L : Program 3) (ctx ty : OTerm α) :
    OTerm α → List (OTerm α) → OTerm α → Prop
  | nil (current : OTerm α) : Rows B Γ g raw L ctx ty current [] current
  | cons {current head out target : OTerm α} {tail : List (OTerm α)} :
      Nonempty (Derivation B Γ (programGraph (advance raw L) (suc out) ![ctx,ty,current,head])) →
      Nonempty (Derivation B Γ (unary g z out)) →
      Rows B Γ g raw L ctx ty (suc out) tail target →
      Rows B Γ g raw L ctx ty current (head :: tail) target

/-- The physical certificate fields use the polynomial sparse code,
not the different Nat.pair codec of iteration scratch. -/
def tape {β : Type} (j : α → β) (hops : List (OTerm α)) (suffix : OTerm β) : OTerm β :=
  hops.foldr (fun h t => rawCons (h.relabel j) t) suffix

def fuelAfter {β : Type} : List (OTerm α) → OTerm β → OTerm β
  | [], n => n
  | _ :: tail, n => fuelAfter tail (suc n)

private theorem tapeRename {β γ : Type} (j : α → β) (k : β → γ)
    (hops : List (OTerm α)) (suffix : OTerm β) :
    (tape j hops suffix).relabel k = tape (k ∘ j) hops (suffix.relabel k) := by
  induction hops with
  | nil => rfl
  | cons h hs ih =>
      change (rawCons (h.relabel j) (tape j hs suffix)).relabel k =
        rawCons (h.relabel (k ∘ j)) (tape (k ∘ j) hs (suffix.relabel k))
      rw [rawConsRename,Term.relabel_relabel,ih]

private theorem fuelRename {β γ : Type} (k : β → γ)
    (hops : List (OTerm α)) (n : OTerm β) :
    (fuelAfter hops n).relabel k = fuelAfter hops (n.relabel k) := by
  induction hops generalizing n with
  | nil => rfl
  | cons h hs ih =>
      change (fuelAfter hs (suc n)).relabel k = fuelAfter hs (suc (n.relabel k))
      rw [ih,sucRelabel]

private theorem keepCompose {β γ : Type} (j : α → β) (k : β → γ)
    (Δ : List (Formula β)) (Θ : List (Formula γ))
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (next : ∀ f ∈ Δ, f.relabel k ∈ Θ) :
    ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Θ := by
  intro f hf
  rw [← formulaRelabelComposition j k f]
  exact next (f.relabel j) (keep f hf)

/-- Advance across the genuine held finite prefix inside a freshly built
packed tape, leaving the exact suffix cursor. The continuation can read
the actual chosen scratch without changing or reflecting the original A. -/
theorem run {g : Program 1} {raw : Program 5} {L : Program 3}
    {ctx ty current target : OTerm α} {hops : List (OTerm α)}
    (rows : Rows B Γ g raw L ctx ty current hops target) :
    ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    ∀ (state fuel start joined suffix : OTerm β) (goal : Formula β),
      Nonempty (Derivation B Δ (loopAt (zeroOutput g (advance raw L))
        state fuel (ctx.relabel j) (ty.relabel j) start joined)) →
      Nonempty (Derivation B Δ (scratchGraph state (tape j hops suffix) (current.relabel j))) →
      (∀ (γ : Type) (k : β → γ) (Θ : List (Formula γ)) (last : OTerm γ),
        (∀ f ∈ Δ, f.relabel k ∈ Θ) →
        Nonempty (Derivation B Θ (loopAt (zeroOutput g (advance raw L)) last
          ((fuelAfter hops fuel).relabel k) (ctx.relabel (k ∘ j)) (ty.relabel (k ∘ j))
          (start.relabel k) (joined.relabel k))) →
        Nonempty (Derivation B Θ (scratchGraph last (suffix.relabel k) (target.relabel (k ∘ j)))) →
        Nonempty (Derivation B Θ (goal.relabel k))) →
      Nonempty (Derivation B Δ goal) := by
  induction rows with
  | nil current =>
      intro β j Δ keep state fuel start joined suffix goal ran held next
      have result := next β id Δ state
        (fun f hf => by simpa only [renameIdentity] using hf)
        (by simpa only [fuelAfter,Term.relabel_id,Function.id_comp] using ran)
        (by simpa only [tape, List.foldr_nil,Term.relabel_id,Function.id_comp] using held)
      simpa only [renameIdentity] using result
  | @cons current head out target tail advanced rank rest ih =>
      intro β j Δ keep state fuel start joined suffix goal ran held next
      let tailTape := tape j tail suffix
      apply scratchCases tailTape (suc (out.relabel j)) goal
      intro γ k Θ nextState keep' scratch
      rw [sucRelabel,tapeRename] at scratch
      let j' := k ∘ j
      have keep'': ∀ f ∈ Γ, f.relabel j' ∈ Θ := keepCompose j k Δ Θ keep keep'
      have ran' := renameInto ran k Θ keep'
      rw [graph5Rename] at ran'
      simp only [Term.relabel_relabel] at ran'
      have held' := renameInto held k Θ keep'
      rw [scratchRename,tapeRename,Term.relabel_relabel] at held'
      have row := moveQuad j' Θ keep'' (advance raw L) (suc out) ctx ty current head advanced
      rw [sucRelabel] at row
      have r := renameInto rank j' Θ keep''
      rw [unaryRename,zRelabel] at r
      let tail' := tape j' tail (suffix.relabel k)
      have cell := NumberedWindowInternalSparsePairGraphProof.consGraph
        (body := B) (Γ := Θ) (head.relabel j') tail'
      have checked := exact_InstallOpenZeroRankOutput g (advance raw L)
        ![ctx.relabel j',ty.relabel j',current.relabel j',head.relabel j'] (out.relabel j') row r
      have step := exact_OpenParameterizedLoopStep (zeroOutput g (advance raw L))
        nextState (state.relabel k) (fuel.relabel k) (ctx.relabel j') (ty.relabel j')
        (start.relabel k) (joined.relabel k) (tape j' (head :: tail) (suffix.relabel k))
        (current.relabel j') (head.relabel j') tail' (suc (out.relabel j')) ran' held' cell checked
        (by simpa only [Term.relabel_relabel] using scratch)
      apply ih γ j' Θ keep'' nextState (suc (fuel.relabel k))
        (start.relabel k) (joined.relabel k) (suffix.relabel k) (goal.relabel k) step
      · simpa only [sucRelabel,Term.relabel_relabel] using scratch
      · intro δ η Λ last pass added final
        have keepAll : ∀ f ∈ Δ, f.relabel (η ∘ k) ∈ Λ := keepCompose k η Θ Λ keep' pass
        have law (f : Formula β) : (f.relabel k).relabel η = f.relabel (η ∘ k) :=
          formulaRelabelComposition k η f
        have fuelEq : (fuelAfter tail (suc (fuel.relabel k))).relabel η =
            (fuelAfter (head :: tail) fuel).relabel (η ∘ k) := by
          simp only [fuelRename, fuelAfter, sucRelabel, Term.relabel_relabel]
        rw [fuelEq] at added
        have answer := next δ (η ∘ k) Λ last keepAll
          (by simpa only [j',Function.comp_assoc,Term.relabel_relabel] using added)
          (by simpa only [j',Function.comp_assoc,Term.relabel_relabel] using final)
        simpa only [law] using answer

/-- Begin the real loop at fuel zero on the actual prefixed tape,
then report its exact held suffix cursor, with the same original proof body. -/
theorem position {g : Program 1} {raw : Program 5} {L : Program 3}
    {ctx ty start target : OTerm α} {hops : List (OTerm α)}
    (rows : Rows B Γ g raw L ctx ty start hops target) (suffix : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (loopAt (zeroOutput g (advance raw L)) state
        ((fuelAfter hops (z : OTerm α)).relabel j) (ctx.relabel j) (ty.relabel j)
        (start.relabel j) ((tape id hops suffix).relabel j))) →
      Nonempty (Derivation B Δ (scratchGraph state (suffix.relabel j) (target.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let joined := tape id hops suffix
  apply scratchCases joined start goal
  intro β j Δ seed keep held
  have initial := exact_OpenParameterizedLoopStart (zeroOutput g (advance raw L)) seed
    (ctx.relabel j) (ty.relabel j) (start.relabel j) (joined.relabel j) held
  have actual : Nonempty (Derivation B Δ (scratchGraph seed
      (tape j hops (suffix.relabel j)) (start.relabel j))) := by
    simpa only [joined,tapeRename,Function.comp_id] using held
  apply run rows β j Δ keep seed z (start.relabel j) (joined.relabel j) (suffix.relabel j)
    (goal.relabel j) initial actual
  intro γ k Θ state moved ran tail
  have allow := keepCompose j k Δ Θ keep moved
  have fuelEq : (fuelAfter hops (z : OTerm β)).relabel k =
      (fuelAfter hops (z : OTerm α)).relabel (k ∘ j) := by
    simp only [fuelRename,zRelabel]
  rw [fuelEq] at ran
  have hit := next γ (k ∘ j) Θ state allow
    (by simpa only [joined,Term.relabel_relabel] using ran)
    (by simpa only [Term.relabel_relabel] using tail)
  simpa only [formulaRelabelComposition] using hit

#print axioms run
#print axioms position
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankLeftTapePositionProof
