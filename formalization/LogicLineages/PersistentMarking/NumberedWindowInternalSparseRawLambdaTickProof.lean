module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaWitnessRoutingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaFrameOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTickProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawLambdaFrame
open NumberedWindowInternalSparseRawLambdaRun
open NumberedWindowInternalSparseRawLambdaFrameOpenProof (literalReports exact_OpenLiteralLambdaFrame)
open NumberedWindowInternalSparseRawLambdaWitnessRoutingProof (exact_OpenLambdaWitnessRouting)
open NumberedWindowInternalSparseRawTick
  (rootTest tagFiveTest rootCall emitState liveTick performLive chosenTick stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickOpenScratchProof (liveRead)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consOfGraph (p q : Program 3) (h t : OTerm α) (xs : Fin 3 → OTerm α)
    (left : Nonempty (Derivation B Γ (programGraph p h xs)))
    (right : Nonempty (Derivation B Γ (programGraph q t xs))) :
    Nonempty (Derivation B Γ (programGraph (consOf p q) (rawCons h t) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0)) (rawCons h t) xs ![h,t]
    (consGraph h t)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

private theorem emitZero (p : Program 3) (f : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph p f xs))) :
    Nonempty (Derivation B Γ (programGraph (emitState (constantZero 3) p) (stateTerm z f) xs)) := by
  have row := consOfGraph p (constantZero 3) f z xs h (constantZeroValue xs)
  exact consOfGraph (constantZero 3) (consOf p (constantZero 3)) z (rawCons f z) xs (constantZeroValue xs) row

private theorem literalFallback (other : Program 3) (dom src child dst : OTerm α) :
    Nonempty (Derivation B Γ (programGraph (lambdaFallback other) (frameValueTerm src child dst)
      (liftedTape dom src child dst))) := by
  let xs := liftedTape dom src child dst
  have notes := literalReports (B := B) (Γ := Γ) dom src child dst
  let rest := ID1Completion.InternalAcceptance.conjunction (onRaw termShape 0)
    (ID1Completion.InternalAcceptance.conjunction (onRaw termShape 2)
      (NumberedWindowInternalSparseRawFunctionFrame.sameSlot 0))
  obtain ⟨guard⟩ := conjunctionRecover lambdaTest rest xs notes.guard
  have next := exact_OpenLiteralLambdaFrame B α Γ dom src child dst
  exact successorBranchIntro lambdaTest other chosenFrame (frameValueTerm src child dst) z xs
    ⟨Derivation.conjunctionLeft guard⟩ next

theorem exact_OpenLambdaLiveTick (p other : Program 3) (dom src child dst : OTerm α) :
    Nonempty (Derivation B Γ (programGraph (liveTick p (lambdaFallback other))
      (stateTerm z (frameValueTerm src child dst)) (liftedTape dom src child dst))) := by
  let xs := liftedTape dom src child dst
  let Q := lambdaFallback other
  let out := stateTerm z (frameValueTerm src child dst)
  obtain ⟨noRoot,noFive⟩ := exact_OpenLambdaWitnessRouting (B := B) (Γ := Γ) dom src child dst
  have h := emitZero Q (frameValueTerm src child dst) xs
    (literalFallback (B := B) (Γ := Γ) other dom src child dst)
  let base := emitState (constantZero 3) Q
  let root := emitState (rootCall p) (constantZero 3)
  let funSide := emitState (constantZero 3) NumberedWindowInternalSparseRawFunctionFrame.chosenFrame
  exact zeroBranchIntro tagFiveTest (branch rootTest base root) funSide out xs noFive
    (zeroBranchIntro rootTest base root out xs noRoot h)

theorem exact_OpenLambdaContextTick : ExactOpenLambdaContextTick := by
  intro B p other α Γ flag dom src child dst
  let orig := liftedTape dom src child dst
  let start := stateTerm flag (frameValueTerm (orig 0) (orig 1) (orig 2))
  let final := stateTerm z (frameValueTerm src child dst)
  let Q := lambdaFallback other
  let xs : Fin 1 → OTerm α := ![start]
  obtain ⟨read,hs,hw,ht⟩ := liveRead (body := B) (Γ := Γ) flag (orig 0) (orig 1) (orig 2)
  have live := exact_OpenLambdaLiveTick (B := B) (Γ := Γ) p other dom src child dst
  have eval : Nonempty (Derivation B Γ (unary (performLive p Q) final start)) := by
    unfold unary performLive
    apply compositionValue (liveTick p Q) ![rowSource,rowWitness,rowDestination] final xs orig live
    intro i
    exact Fin.cases hs (Fin.cases hw (Fin.cases ht (fun q => Fin.elim0 q))) i
  exact successorBranchIntro stateFrame (.projection 0) (performLive p Q) final
    (packedBody [orig 0,orig 1,orig 2]) xs read eval

#print axioms exact_OpenLambdaLiveTick
#print axioms exact_OpenLambdaContextTick
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTickProof
