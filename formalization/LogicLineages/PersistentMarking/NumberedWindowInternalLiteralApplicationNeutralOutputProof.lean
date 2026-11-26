module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationNeutralOutputProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalRecursionGraphExtensionSupportProof (successorOrder)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralNeutralAtomProof
  (neutralSource rawHeader neutralFromHeader zeroBelowSuccessor)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastKeeps)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A genuine application report uses the physical tag-six seed.
The selected top-tag guard preserves that actual tag at the returned
least, so the result passes the literal neutral test without an
external type interpretation. This is not a scalar admission proof. -/
theorem neutralOfReport (L : Program 3) (c dom cod fn arg y : OTerm α)
    (h : D B Γ (outputReport (guardedLeast (headerLeast L)) c cod (auxiliaryTerm dom cod fn arg) y)) :
    D B Γ (atom neutralSource y) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let c' := c.relabel j
  let cod' := cod.relabel j
  let y' := y.relabel j
  let seed := (auxiliaryTerm dom cod fn arg).relabel j
  let A := programGraph (guardedLeast (headerLeast L)) (suc k) ![c',cod',seed] ⊓
    eqn y' (addressTerm c' cod' k)
  let Δ := A :: Γ.map weaken
  have row : Derivation B Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨bundle⟩ := exact_OpenAtomicLeastReport (headerLeast L) c' cod' seed k
    ⟨Derivation.conjunctionLeft row⟩
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Δ) (numeral 6)
    (rawCons (dom.relabel j) (rawCons cod' (rawCons (fn.relabel j) (rawCons (arg.relabel j) z))))
  have tag : D B Δ (programGraph cellHead (numeral 6) ![seed]) := by
    simp only [seed,auxiliaryTerm,rawConsRename,numeralRename,zRelabel,cod']
    exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have kept := exact_OpenLiteralHeaderLeastKeeps L c' cod' seed k (numeral 6)
    ⟨Derivation.conjunctionLeft bundle⟩ tag
  let addr := addressTerm c' cod' k
  obtain ⟨good,_,_,raw⟩ := literalAddress (body := B) (Γ := Δ) c' cod' k
  have header := makeUnary cellHead rawLeast (numeral 6) addr k kept raw
  have less : D B Δ (ltF (numeral 2 : OTerm (α ⊕ Fin 1)) (numeral 6)) :=
    successorOrder (numeral 1) (numeral 5)
      (successorOrder (numeral 0) (numeral 4) (zeroBelowSuccessor (numeral 3)))
  have neutral := neutralFromHeader addr (numeral 6) good header
    (rejectBackwardOrder (numeral 6) (numeral 2) less)
  have final : D B Δ (atom neutralSource y') :=
    headTransport neutralSource (suc z) addr y' ![] ⟨symm (Derivation.conjunctionRight row)⟩ neutral
  obtain ⟨read⟩ := h
  have relabeled : D B Δ ((atom neutralSource y).relabel j) := by
    rw [atomRename]
    exact final
  obtain ⟨out⟩ := relabeled
  exact ⟨Derivation.existentialElimination read out⟩

theorem exact_OpenLiteralApplicationNeutralOutput (i : Program 1) (L : Program 3)
    (f u y : OTerm α)
    (h : D B Γ (programGraph (applicationGuard i (guardedLeast (headerLeast L))) (suc z) ![f,u,y])) :
    D B Γ (atom neutralSource y) := by
  let least := guardedLeast (headerLeast L)
  obtain ⟨row⟩ := forward i least f u y h
  apply rowCases least f u y (atom neutralSource y)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight row)⟩
  intro β j Δ c result dom cod fn arg keep reported
  rw [atomRename]
  obtain ⟨got⟩ := reported
  exact neutralOfReport L c dom cod fn arg (y.relabel j) ⟨Derivation.conjunctionRight got⟩

#print axioms exact_OpenLiteralApplicationNeutralOutput
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationNeutralOutputProof
