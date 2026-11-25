module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallLeafProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRuleCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody rawConsRename unaryRename)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawTick (stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root shapes)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralDirectRootSuccessProof (exact_OpenLiteralDirectRootSuccessCases)
open NumberedWindowInternalLiteralRootCallLeafProof (exact_OpenLiteralRootCallLeafCases)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

private theorem twoInputsRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

/-- Recover the actual literal rule, its ordered payload, and the
preceding scratch reports from a direct certificate of the installed
body. The first and reached tapes remain distinct; the callback gets
the original iterator graph that relates them, not a numerical claim
that their sources or destinations agree. -/
theorem exact_OpenLiteralDirectRuleCases (i cv tv : Program 1)
    (leaf : Nat → Program 3) (other window L : Program 3) (V : Program 1)
    (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let p := root leaf
    let raw := typedRaw5 p other window V
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (direct data (hop cv tv R L) c x y) →
    (∀ tag arity, (tag,arity) ∈ shapes →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (q w r u prev frame payload : OTerm β) (tape : Fin 3 → OTerm β) (fields : List (OTerm β)),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) → fields.length = arity →
      D B Δ (programGraph (iterateState p other) prev ![u,stateTerm z (frameValueTerm q w r)]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (frameSlot 0 1) payload tape) →
      D B Δ (eqn payload (rawCons (numeral tag) (packedBody fields))) →
      D B Δ (bit (leaf tag) ![tape 0,payload,tape 2]) →
      D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro p raw R data B edge use
  apply exact_OpenLiteralDirectRootSuccessCases i cv tv p other window L V c x y goal edge
  intro β j Δ q w r u prev frame tape keep prior available left path right hit
  apply exact_OpenLiteralRootCallLeafCases leaf tape (goal.relabel j) hit
  intro tag arity known γ l Ω payload fields stay size selected equation rule
  let m := l ∘ j
  let ts := fun a => (tape a).relabel l
  have retain (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep φ mem)
  have run := renameInto prior l Ω stay
  simp only [programRename,twoInputsRename,stateRename,frameValueTerm,sucRelabel,rawConsRename,zRelabel] at run
  have live := renameInto available l Ω stay
  have q' := renameInto left l Ω stay
  have w' := renameInto path l Ω stay
  have r' := renameInto right l Ω stay
  simp only [unaryRename,sucRelabel] at live q' w' r'
  have reply := use tag arity known γ m Ω (q.relabel l) (w.relabel l) (r.relabel l) (u.relabel l)
    (prev.relabel l) (frame.relabel l) payload ts fields retain size run live q' w' r' selected equation rule
  simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenLiteralDirectRuleCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRuleCasesProof
