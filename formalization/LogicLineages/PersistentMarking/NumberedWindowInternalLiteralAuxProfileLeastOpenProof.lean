module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique outputTransport compositionValue)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralAuxProfileLeastProof
open NumberedWindowInternalLiteralAtomicLeastGuardProof (outRaw pairFirst)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D rejectZeroOutput outReport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem keepOriginal (q code t : OTerm α)
    (h : D B Γ (programGraph retainAuxProfile (suc t) ![q,code])) :
    D B Γ (eqn code (suc t)) := by
  apply optionGraphCases auxProfileTest ![q,code] (eqn code (suc t))
  · intro β j Δ keep no
    rw [pairRename] at no
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    exact rejectZeroOutput _ _ _
      (zeroBranchElim auxProfileTest (constantZero 2) (.projection 1) _ _ no held)
  · intro β j Δ k keep yes
    rw [eqnRelabel,sucRelabel]
    rw [pairRename] at yes
    let xs : Fin 2 → OTerm β := ![q.relabel j,code.relabel j]
    have held := renameInto h j Δ keep
    simp only [programRename,pairRename,sucRelabel] at held
    have read := successorBranchElim auxProfileTest (constantZero 2) (.projection 1) (suc (t.relabel j))
      k xs yes held
    exact valueUnique (.projection 1) (code.relabel j) (suc (t.relabel j)) xs
      (projectionValue 1 xs) read

/-- Remove the exact physical auxiliary-profile guard without changing the
selected least result. The added check also remains available on
the real input and the same successful encoded output. -/
theorem exact_OpenLiteralAuxProfileLeastReport (L : Program 3) (ctx ty q t : OTerm α)
    (h : D B Γ (programGraph (auxProfileLeast L) (suc t) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc t) ![ctx,ty,q] ⊓ programGraph retainAuxProfile (suc t) ![q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let select : Fin 2 → Program 3 := Fin.cons (.projection 2) (Fin.cons L Fin.elim0)
  have least : D B Γ (programGraph L (suc t) xs) := by
    apply programCases L xs (programGraph L (suc t) xs)
    intro β j Δ code keep chosen
    simp only [xs,programRename,tripleInputsRename,sucRelabel]
    simp only [xs,tripleInputsRename] at chosen
    let x' : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,q.relabel j]
    have edge := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at edge
    have gate : D B Δ (programGraph retainAuxProfile (suc (t.relabel j)) ![q.relabel j,code]) := by
      apply compositionRecover retainAuxProfile select (suc (t.relabel j)) x' ![q.relabel j,code] edge
      intro k
      exact Fin.cases (projectionValue 2 x') (Fin.cases chosen (fun e => Fin.elim0 e)) k
    exact outputTransport L code (suc (t.relabel j)) x'
      (keepOriginal (q.relabel j) code (t.relabel j) gate) chosen
  have actual : D B Γ (programGraph retainAuxProfile (suc t) ![q,suc t]) := by
    apply compositionRecover retainAuxProfile select (suc t) xs ![q,suc t] h
    intro k
    exact Fin.cases (projectionValue 2 xs) (Fin.cases least (fun e => Fin.elim0 e)) k
  obtain ⟨l⟩ := least
  obtain ⟨g⟩ := actual
  exact ⟨Derivation.conjunctionIntroduction l g⟩

/-- A successful retained output requires actual unit on the profile
test, since a rejected physical conjunction selects actual zero. -/
theorem exact_OpenAuxProfileTest (q t : OTerm α)
    (held : D B Γ (programGraph retainAuxProfile (suc t) ![q,suc t])) :
    D B Γ (programGraph auxProfileTest (suc z) ![q,suc t]) := by
  let xs : Fin 2 → OTerm α := ![q,suc t]
  let yes := programGraph auxProfileTest (suc z) xs
  obtain ⟨out⟩ := held
  have bad : D B (yes.not :: Γ) yes := by
    have denied : D B (yes.not :: Γ) yes.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero : D B (yes.not :: Γ) (programGraph auxProfileTest z xs) :=
      conjunctionReject (matchCoordinates termShape) auxFieldsIfPresent xs denied
    exact rejectZeroOutput _ _ _
      (zeroBranchElim auxProfileTest (constantZero 2) (.projection 1) (suc t) xs zero
        ⟨addHyp out _⟩)
  obtain ⟨excluded⟩ := bad
  exact ⟨disjunctionElimination (excludedMiddle yes)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction excluded)⟩

private theorem atSource (p : Program 1) (q t val : OTerm α)
    (h : D B Γ (programGraph p val ![q])) :
    D B Γ (programGraph (pairFirst p) val ![q,suc t]) := by
  let xs : Fin 2 → OTerm α := ![q,suc t]
  apply compositionValue p (Fin.cons (.projection 0) Fin.elim0) val xs ![q] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue 0 xs

/-- Read any of the four individual comparisons from its actual two
raw-coordinate graphs. The right input is decoded from the original
successor-encoded output slot, not chosen independently. -/
theorem exact_OpenLiteralAuxCoordinateEquality (p : Program 1) (q t a b : OTerm α)
    (src : D B Γ (programGraph p a ![q])) (dst : D B Γ (programGraph p b ![t]))
    (h : D B Γ (programGraph (matchCoordinates p) (suc z) ![q,suc t])) :
    D B Γ (eqn a b) := by
  let xs : Fin 2 → OTerm α := ![q,suc t]
  have v : D B Γ (programGraph (decodedOutput p) b xs) := by
    apply compositionValue p (Fin.cons outRaw Fin.elim0) b xs ![t] dst
    intro k
    obtain rfl := Fin.eq_zero k
    exact outReport q t
  unfold matchCoordinates at h
  rw [exact_DispatchControlAST.2.2.2.1] at h
  have compared := compositionRecover equalityTest (Fin.cons (pairFirst p) (Fin.cons (decodedOutput p) Fin.elim0))
    (suc z) xs (Fin.cons a (Fin.cons b Fin.elim0)) h
    (fun j => Fin.cases (atSource p q t a src) (Fin.cases v (fun e => Fin.elim0 e)) j)
  exact equalityOfAcceptance a b compared

/-- Both directions of actual auxiliary shape transport. -/
theorem exact_OpenLiteralAuxCoordinateTransfer (p : Program 1) (q t a : OTerm α)
    (h : D B Γ (programGraph (matchCoordinates p) (suc z) ![q,suc t])) :
    (D B Γ (programGraph p a ![q]) → D B Γ (programGraph p a ![t])) ∧
    (D B Γ (programGraph p a ![t]) → D B Γ (programGraph p a ![q])) := by
  constructor
  · intro left
    apply programCases p ![t] _
    intro β j Δ v keep right
    rw [programRename,inputsRename]
    rw [inputsRename] at right
    have l := renameInto left j Δ keep
    have match' := renameInto h j Δ keep
    simp only [programRename,inputsRename] at l
    simp only [programRename,pairRename,sucRelabel,zRelabel] at match'
    obtain ⟨e⟩ := exact_OpenLiteralAuxCoordinateEquality p (q.relabel j) (t.relabel j)
      (a.relabel j) v l right match'
    exact outputTransport p v (a.relabel j) ![t.relabel j] ⟨symm e⟩ right
  · intro right
    apply programCases p ![q] _
    intro β j Δ v keep left
    rw [programRename,inputsRename]
    rw [inputsRename] at left
    have r := renameInto right j Δ keep
    have match' := renameInto h j Δ keep
    simp only [programRename,inputsRename] at r
    simp only [programRename,pairRename,sucRelabel,zRelabel] at match'
    have e := exact_OpenLiteralAuxCoordinateEquality p (q.relabel j) (t.relabel j)
      v (a.relabel j) left r match'
    exact outputTransport p v (a.relabel j) ![q.relabel j] e left

theorem exact_OpenLiteralAuxProfileShape (L : Program 3) (ctx ty q t : OTerm α)
    (held : D B Γ (programGraph (auxProfileLeast L) (suc t) ![ctx,ty,q])) :
    (D B Γ (programGraph termShape (suc z) ![q]) → D B Γ (programGraph termShape (suc z) ![t])) ∧
    (D B Γ (programGraph termShape (suc z) ![t]) → D B Γ (programGraph termShape (suc z) ![q])) := by
  obtain ⟨row⟩ := exact_OpenLiteralAuxProfileLeastReport L ctx ty q t held
  obtain ⟨profile⟩ := conjunctionRecover (matchCoordinates termShape) auxFieldsIfPresent ![q,suc t]
    (exact_OpenAuxProfileTest q t ⟨Derivation.conjunctionRight row⟩)
  exact exact_OpenLiteralAuxCoordinateTransfer termShape q t (suc z) ⟨Derivation.conjunctionLeft profile⟩

theorem exact_OpenLiteralAuxProfileFields (L : Program 3) (ctx ty q t : OTerm α)
    (held : D B Γ (programGraph (auxProfileLeast L) (suc t) ![ctx,ty,q]))
    (isAux : D B Γ (programGraph termShape (suc z) ![q])) :
    D B Γ (programGraph (matchCoordinates (field 0)) (suc z) ![q,suc t] ⊓
      (programGraph (matchCoordinates (field 1)) (suc z) ![q,suc t] ⊓
        programGraph (matchCoordinates functionHead) (suc z) ![q,suc t])) := by
  obtain ⟨row⟩ := exact_OpenLiteralAuxProfileLeastReport L ctx ty q t held
  obtain ⟨profile⟩ := conjunctionRecover (matchCoordinates termShape) auxFieldsIfPresent ![q,suc t]
    (exact_OpenAuxProfileTest q t ⟨Derivation.conjunctionRight row⟩)
  have fields := successorBranchElim (pairFirst termShape) (constantOne 2) fieldMatch
    (suc z) z ![q,suc t] (atSource termShape q t (suc z) isAux) ⟨Derivation.conjunctionRight profile⟩
  exact conjunctionRecover (matchCoordinates (field 0))
    (conjunction (matchCoordinates (field 1)) (matchCoordinates functionHead)) ![q,suc t] fields |>.elim
    (fun proof => by
      obtain ⟨rest⟩ := conjunctionRecover (matchCoordinates (field 1)) (matchCoordinates functionHead)
        ![q,suc t] ⟨Derivation.conjunctionRight proof⟩
      exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft proof) rest⟩)

#print axioms exact_OpenLiteralAuxProfileLeastReport
#print axioms exact_OpenAuxProfileTest
#print axioms exact_OpenLiteralAuxCoordinateEquality
#print axioms exact_OpenLiteralAuxCoordinateTransfer
#print axioms exact_OpenLiteralAuxProfileShape
#print axioms exact_OpenLiteralAuxProfileFields
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
