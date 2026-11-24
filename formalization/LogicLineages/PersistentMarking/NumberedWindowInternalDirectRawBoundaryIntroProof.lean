module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawBoundaryIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consValue)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename parserRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape)
open NumberedWindowInternalDirectRawSourceIntroProof (Report exact_OriginalRawSourceFromDecoded)
open NumberedWindowInternalDirectBoundaryGuardsTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem presentSuc (x : OTerm α) :
    Report (B := B) (Γ := Γ) presentScratch (suc z) ![suc x] :=
  successorBranchIntro (.projection 0) (constantZero 1) (constantOne 1) (suc z) x ![suc x]
    (projectionValue 0 ![suc x]) (oneConstantValue ![suc x])

/-- The same original nonempty guard accepts an actual reported
scratch cons; no numeric test or alternate remove criterion is added. -/
theorem exact_OriginalPresentScratchFromCons (code h t : OTerm α)
    (c : Nonempty (Derivation B Γ (consGraph code h t))) :
    Nonempty (Derivation B Γ (unary presentScratch (suc z) code)) := by
  apply programCases ID1Completion.InternalPairing.pairing ![h,t] _
  intro β j Δ p keep pair
  rw [binaryInputsRename] at pair
  rw [unaryRename,sucRelabel,zRelabel]
  let cd := code.relabel j
  let hh := h.relabel j
  let tt := t.relabel j
  have c' := renamePair consCode code h t c j keep
  have canonical : Report (B := B) (Γ := Δ) consCode (suc p) ![hh,tt] :=
    consValue p hh tt pair
  have e := valueUnique consCode (suc p) cd ![hh,tt] canonical c'
  exact headTransport presentScratch (suc z) (suc p) cd Fin.elim0 e (presentSuc p)

private theorem located (p : Program 1) (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (h : Report (B := B) (Γ := Γ) p out ![xs i]) :
    Report (B := B) (Γ := Γ) (atSlot p i) out xs := by
  apply compositionValue p ![.projection i] out xs ![xs i] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

theorem exact_OriginalRawBoundaryFromReports (i : Program 1)
    (s t d ds dt dd h tail : OTerm α)
    (parts : BoundaryReports B Γ s t d ds dt dd h tail i) :
    Report (B := B) (Γ := Γ) (boundaryRaw i) (suc z) (sourceTape s t d) := by
  let ys := sourceTape ds dt dd
  have first := located (typedScratch i) 0 ys (suc z) parts.sourceTyped
  have second := located (typedScratch i) 1 ys (suc z) parts.targetTyped
  have third := located presentScratch 2 ys (suc z)
    (exact_OriginalPresentScratchFromCons dd h tail parts.removedCons)
  have core : Report (B := B) (Γ := Γ) (boundaryScratch i) (suc z) ys :=
    conjunctionAccept (atSlot (typedScratch i) 0)
      (conjunction (atSlot (typedScratch i) 1) (atSlot presentScratch 2)) ys first
      (conjunctionAccept (atSlot (typedScratch i) 1) (atSlot presentScratch 2) ys second third)
  exact exact_OriginalRawSourceFromDecoded (boundaryScratch i) s t d ds dt dd parts.parsed core

#print axioms exact_OriginalPresentScratchFromCons
#print axioms exact_OriginalRawBoundaryFromReports
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawBoundaryIntroProof
