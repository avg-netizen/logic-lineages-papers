module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickOpenScratchProof (liveRead)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The unary test underneath the actual literal tag shape is an
original conjunction. A rejected call has output exactly zero. -/
theorem shapeReject (tag : Program 1) (arity : Nat) (i : Fin 3) (xs : Fin 3 → OTerm α)
    (h : D B Γ (programGraph (onRaw (nodeGood tag arity) i) (suc z) xs).not) :
    D B Γ (programGraph (onRaw (nodeGood tag arity) i) z xs) := by
  let g := nodeGood tag arity
  let a := unary g (suc z) (xs i)
  obtain ⟨notA⟩ := h
  have yes : D B (a :: Γ) (programGraph (onRaw g i) (suc z) xs) :=
    onTape g i (suc z) xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨wouldContradict⟩ := yes
  have no : D B Γ a.not := ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp notA a) wouldContradict)⟩
  have none : D B Γ (unary g z (xs i)) := by
    unfold g nodeGood
    exact conjunctionReject _ _ ![xs i] no
  exact onTape g i z xs none

/-- Lift a report of the exact live dispatcher to its actual first tick
at the original raw initial scratch. All raw tape entries are retained. -/
theorem initialTick (p other : Program 3) (q w r out : OTerm α)
    (live : D B Γ (programGraph (liveTick p other) out ![q,w,r])) :
    D B Γ (programGraph (chosenTick p other) out ![initialTerm (![q,w,r])]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let start := initialTerm xs
  let one : Fin 1 → OTerm α := ![start]
  obtain ⟨hf,hq,hw,hr⟩ := liveRead (body := B) (Γ := Γ) z q w r
  have after : D B Γ (programGraph (performLive p other) out one) := by
    unfold performLive
    apply compositionValue (liveTick p other) ![rowSource,rowWitness,rowDestination] out one xs live
    intro i
    exact Fin.cases hq (Fin.cases hw (Fin.cases hr (fun j => Fin.elim0 j))) i
  exact successorBranchIntro stateFrame (.projection 0) (performLive p other) out
    (packedBody [q,w,r]) one hf after

#print axioms shapeReject
#print axioms initialTick
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
