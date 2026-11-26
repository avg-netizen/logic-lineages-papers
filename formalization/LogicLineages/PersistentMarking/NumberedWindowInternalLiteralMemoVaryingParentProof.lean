module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoVaryingParentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (refl cancelSuc)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoParentIntroProof (exact_OpenTypedMemoAuxiliaryIntro)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph packedLeastOn)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def varyingOperandType {α : Type} (varyArgument : Bool) (dom cod : OTerm α) : OTerm α :=
  if varyArgument then dom else rawCons dom cod

theorem exact_MemoVaryingTypeRename {β : Type} (v : Bool) (d c : OTerm α) (j : α → β) :
    (varyingOperandType v d c).relabel j = varyingOperandType v (d.relabel j) (c.relabel j) := by
  cases v
  · exact rawConsRename d c j
  · rfl

/-- Introducing the selected parent is now paid by the single actual
base parent edge and the actual selected child. The argument case is
an exchange of representatives, not a raw reduction. -/
theorem exact_OpenTypedMemoVaryingParent (Base : Program 4) (reverse : CanReverse Base)
    (v : Bool) (ctx dom cod q r fixed : OTerm α)
    (parent : D B Γ (acceptEdge Base ctx cod (varyAuxiliary v dom cod q fixed)
      (varyAuxiliary v dom cod r fixed)))
    (child : D B Γ (acceptEdge (recursiveTypedMemo Base) ctx (varyingOperandType v dom cod) q r)) :
    D B Γ (acceptEdge (recursiveTypedMemo Base) ctx cod (varyAuxiliary v dom cod q fixed)
      (varyAuxiliary v dom cod r fixed)) := by
  obtain ⟨arc⟩ := child
  cases v
  · let a : AuxRow α := ⟨dom,cod,q,fixed⟩
    let b : AuxRow α := ⟨dom,cod,r,fixed⟩
    exact exact_OpenTypedMemoAuxiliaryIntro Base reverse ctx cod a b parent ⟨refl dom⟩ ⟨refl cod⟩
      ⟨orLeft (Derivation.conjunctionIntroduction arc (refl fixed))⟩
  · let a : AuxRow α := ⟨dom,cod,fixed,q⟩
    let b : AuxRow α := ⟨dom,cod,fixed,r⟩
    exact exact_OpenTypedMemoAuxiliaryIntro Base reverse ctx cod a b parent ⟨refl dom⟩ ⟨refl cod⟩
      ⟨orRight (Derivation.conjunctionIntroduction (refl fixed) arc)⟩

def BaseApplicationLiftAt (Base : Program 4) (v : Bool) (B : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ctx dom cod fixed : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q r : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    D B Δ (acceptEdge (recursiveTypedMemo Base) (ctx.relabel j)
      (varyingOperandType v (dom.relabel j) (cod.relabel j)) q r) →
    D B Δ (acceptEdge Base (ctx.relabel j) (cod.relabel j)
      (varyAuxiliary v (dom.relabel j) (cod.relabel j) q (fixed.relabel j))
      (varyAuxiliary v (dom.relabel j) (cod.relabel j) r (fixed.relabel j)))

#print axioms exact_MemoVaryingTypeRename
#print axioms exact_OpenTypedMemoVaryingParent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoVaryingParentProof
