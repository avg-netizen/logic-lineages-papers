module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoVaryingParentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoParentIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportCoreProof
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
open NumberedWindowInternalLiteralMemoRoundApplicationSelectedProof (exact_OpenMemoSelectedApplication)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph packedLeastOn)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)

open NumberedWindowInternalLiteralMemoVaryingParentProof

attribute [local irreducible] programGraph packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def SelectedParentEdgesAt (E : Program 4) (v : Bool) (B : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (ctx dom cod fixed : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q r : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    D B Δ (acceptEdge E (ctx.relabel j)
      (varyingOperandType v (dom.relabel j) (cod.relabel j)) q r) →
    D B Δ (acceptEdge E (ctx.relabel j) (cod.relabel j)
      (varyAuxiliary v (dom.relabel j) (cod.relabel j) q (fixed.relabel j))
      (varyAuxiliary v (dom.relabel j) (cod.relabel j) r (fixed.relabel j)))

private theorem initialMotive (C : Program 3) (E : Program 4) (v : Bool) (s : Settings)
    (ctx dom cod fixed seed k : OTerm α)
    (least : D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod seed fixed) k)) :
    D B Γ (appMotive (constantZero 1) C E v s ctx cod dom cod fixed z k seed) := by
  have z0 : D B Γ (programGraph (constantZero 1) z ![seed]) := zeroConstantValue ![seed]
  obtain ⟨zero⟩ := z0
  obtain ⟨given⟩ := least
  exact ⟨Derivation.conjunctionIntroduction zero given⟩

private theorem edgeMotive (C : Program 3) (E : Program 4) (v : Bool) (s : Settings)
    (ctx dom cod fixed k : OTerm α)
    (stable : Preserves E (packedLeastOn C E s))
    (lift : SelectedParentEdgesAt E v B Γ ctx dom cod fixed) :
    ApplicationEdgeStepAt E (constantZero 1) C E v s B Γ ctx (varyingOperandType v dom cod)
      ctx cod dom cod fixed z k := by
  intro β j Δ q r keep edge source
  rw [exact_MemoVaryingTypeRename] at edge
  let c := ctx.relabel j
  let d := dom.relabel j
  let e := cod.relabel j
  let a := fixed.relabel j
  let q' := varyAuxiliary v d e q a
  let r' := varyAuxiliary v d e r a
  let value := k.relabel j
  obtain ⟨given⟩ := source
  have read : D B Δ (observe (packedLeastOn C E s) c e q' (suc value)) :=
    ⟨Derivation.conjunctionRight given⟩
  have accepted := lift β j Δ q r keep edge
  have output : D B Δ (observe (packedLeastOn C E s) c e r' (suc value)) :=
    stable B β Δ c e q' r' (suc value) accepted read
  have lit : D B Δ (programGraph (constantZero 1) z ![r]) := zeroConstantValue ![r]
  rw [zRelabel]
  obtain ⟨lit⟩ := lit
  obtain ⟨output⟩ := output
  exact ⟨Derivation.conjunctionIntroduction lit output⟩

/-- One checked parent lift along each actual typed child edge suffices
to carry the parent's least report along the chosen original rounds. -/
theorem exact_OpenSelectedParentRoundTransport (C : Program 3) (E : Program 4) (s : Settings)
    (stable : Preserves E (packedLeastOn C E s))
    (v : Bool) (ctx dom cod seed chosen fixed m : OTerm α)
    (lift : SelectedParentEdgesAt E v B Γ ctx dom cod fixed)
    (child : D B Γ (leastOnGraph C E s ctx (varyingOperandType v dom cod) seed chosen))
    (parent : D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod seed fixed) m)) :
    D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod chosen fixed) m) := by
  have given := initialMotive C E v s ctx dom cod fixed seed m parent
  have moves := edgeMotive C E v s ctx dom cod fixed m stable lift
  obtain ⟨result⟩ := exact_OpenMemoSelectedApplication C E s (constantZero 1) C E v s
    ctx (varyingOperandType v dom cod) seed chosen ctx cod dom cod fixed z m moves given child
  exact ⟨Derivation.conjunctionRight result⟩

#print axioms exact_OpenSelectedParentRoundTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportCoreProof
