module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomOnEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomGuardOnProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename projectionValue compositionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc symm sucNeZeroApply zeroNeSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralAtomicLeastGuardProof
open NumberedWindowInternalLiteralAtomOnEdgeProof
open NumberedWindowInternalLiteralAtomicLeastOpenProof (outReport)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (q k : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![q,k] : Fin 2 → OTerm α) i).relabel j) = ![q.relabel j,k.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun impossible => Fin.elim0 impossible)) i

private theorem allowedForSame (q k : OTerm α) (same : D B Γ (eqn q k)) :
    D B Γ (programGraph keepAtom (suc k) ![q,suc k]) := by
  let xs : Fin 2 → OTerm α := ![q,suc k]
  have cmp : D B Γ (programGraph checkSame (suc z) xs) := by
    unfold checkSame
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest (Fin.cons (.projection 0) (Fin.cons outRaw Fin.elim0))
      (suc z) xs (Fin.cons q (Fin.cons k Fin.elim0)) (equalityOfEqual q k same)
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (outReport q k) (fun n => Fin.elim0 n)) i
  exact successorBranchIntro checkSame (constantZero 2) (.projection 1) (suc k) z xs cmp (projectionValue 1 xs)

private theorem atomOutputSame (q k : OTerm α) (same : D B Γ (eqn q k)) :
    D B Γ (programGraph atomOutput (suc k) ![q,suc k]) := by
  apply optionGraphCases checkAtom ![q,suc k] _
  · intro β j Δ keep absent
    simp only [programRename,pairRename,sucRelabel]
    simp only [pairRename,sucRelabel] at absent
    let xs : Fin 2 → OTerm β := ![q.relabel j,suc (k.relabel j)]
    exact zeroBranchIntro checkAtom (.projection 1) keepAtom (suc (k.relabel j)) xs absent
      (projectionValue 1 xs)
  · intro β j Δ p keep yes
    simp only [programRename,pairRename,sucRelabel]
    simp only [pairRename,sucRelabel] at yes
    have eq := renameInto same j Δ keep
    rw [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel] at eq
    let xs : Fin 2 → OTerm β := ![q.relabel j,suc (k.relabel j)]
    exact successorBranchIntro checkAtom (.projection 1) keepAtom (suc (k.relabel j)) p xs yes
      (allowedForSame (q.relabel j) (k.relabel j) eq)

private theorem atomOutputNeither (q k : OTerm α) (qNo : D B Γ (unary atomicTest z q))
    (kNo : D B Γ (unary atomicTest z k)) : D B Γ (programGraph atomOutput (suc k) ![q,suc k]) := by
  let xs : Fin 2 → OTerm α := ![q,suc k]
  have a : D B Γ (programGraph (pairFirst atomicTest) z xs) := by
    apply compositionValue atomicTest (Fin.cons (.projection 0) Fin.elim0) z xs ![q] qNo
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have b : D B Γ (programGraph outAtom z xs) := by
    apply compositionValue atomicTest (Fin.cons outRaw Fin.elim0) z xs ![k] kNo
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport q k
  have no : D B Γ (programGraph checkAtom z xs) :=
    zeroBranchIntro (pairFirst atomicTest) outAtom
      (NumberedWindowInternalFreshProbeDispatchProgram.literal 2 1) z xs a b
  exact zeroBranchIntro checkAtom (.projection 1) keepAtom (suc k) xs no (projectionValue 1 xs)

private theorem onRight (q k v : OTerm α)
    (qRead : D B Γ (unary atomicStamp v q)) (kRead : D B Γ (unary atomicStamp v k))
    (qZero : D B Γ (unary atomicTest z q) ∨ D B Γ (eqn v (suc q))) :
    D B Γ (programGraph atomOutput (suc k) ![q,suc k]) := by
  apply optionGraphCases atomicTest ![k] _
  · intro β j Δ keep absent
    simp only [programRename,pairRename,sucRelabel]
    rw [unaryInputsRename] at absent
    let a := q.relabel j
    let b := k.relabel j
    let value := v.relabel j
    rcases qZero with left | right
    · have zq := renameInto left j Δ keep
      rw [unaryRename,ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at zq
      exact atomOutputNeither a b zq absent
    · have e := renameInto right j Δ keep
      rw [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel] at e
      have actual := renameInto kRead j Δ keep
      rw [unaryRename] at actual
      obtain ⟨no⟩ := valueUnique atomicStamp value z ![b] actual (exact_OpenAtomStampZero b absent)
      obtain ⟨pos⟩ := e
      exact ⟨Derivation.explosion (sucNeZeroApply
        (ID1Completion.InternalTagArithmeticSupportProof.trans (symm pos) no))⟩
  · intro β j Δ event keep active
    simp only [programRename,pairRename,sucRelabel]
    rw [unaryInputsRename] at active
    let a := q.relabel j
    let b := k.relabel j
    let value := v.relabel j
    have actual := renameInto kRead j Δ keep
    rw [unaryRename] at actual
    obtain ⟨positive⟩ := valueUnique atomicStamp value (suc b) ![b] actual (exact_OpenAtomStampPositive b event active)
    rcases qZero with left | right
    · have aq := renameInto qRead j Δ keep
      rw [unaryRename] at aq
      have zq := renameInto left j Δ keep
      rw [unaryRename,ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at zq
      obtain ⟨zero⟩ := valueUnique atomicStamp value z ![a] aq (exact_OpenAtomStampZero a zq)
      exact ⟨Derivation.explosion (zeroNeSuc (ID1Completion.InternalTagArithmeticSupportProof.trans (symm zero) positive))⟩
    · have e := renameInto right j Δ keep
      rw [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel] at e
      obtain ⟨eq⟩ := e
      exact atomOutputSame a b ⟨cancelSuc (ID1Completion.InternalTagArithmeticSupportProof.trans (symm eq) positive)⟩

theorem exact_OpenAtomOutputFromStamps (q k v : OTerm α)
    (left : D B Γ (unary atomicStamp v q)) (right : D B Γ (unary atomicStamp v k)) :
    D B Γ (programGraph atomOutput (suc k) ![q,suc k]) := by
  apply optionGraphCases atomicTest ![q] _
  · intro β j Δ keep zero
    simp only [programRename,pairRename,sucRelabel]
    rw [unaryInputsRename] at zero
    have l := renameInto left j Δ keep
    have r := renameInto right j Δ keep
    rw [unaryRename] at l r
    exact onRight (q.relabel j) (k.relabel j) (v.relabel j) l r (.inl zero)
  · intro β j Δ event keep active
    simp only [programRename,pairRename,sucRelabel]
    rw [unaryInputsRename] at active
    have l := renameInto left j Δ keep
    have r := renameInto right j Δ keep
    rw [unaryRename] at l r
    have same := valueUnique atomicStamp (v.relabel j) (suc (q.relabel j)) ![q.relabel j] l
      (exact_OpenAtomStampPositive (q.relabel j) event active)
    exact onRight (q.relabel j) (k.relabel j) (v.relabel j) l r (.inr same)

theorem exact_OpenAtomGuardFromValue (L : Program 3) (ctx ty q k v : OTerm α)
    (held : D B Γ (programGraph L (suc k) ![ctx,ty,q]))
    (left : D B Γ (unary atomicStamp v q)) (right : D B Γ (unary atomicStamp v k)) :
    D B Γ (programGraph (guardedLeast L) (suc k) ![ctx,ty,q]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  apply compositionValue atomOutput (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))
    (suc k) xs ![q,suc k] (exact_OpenAtomOutputFromStamps q k v left right)
  exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases held (fun n => Fin.elim0 n)) i

/-- Keep a genuine successful report from any wrapper after installing
the literal atomic guard, provided the same physically selected least
is used for sourcing the second atom-stamp witness. -/
theorem exact_OpenAtomGuardOnEdge (C : Program 3) (E : Program 4) (s : Settings) (L : Program 3)
    (stable : Preserves E atomObserver) (ctx ty q k v : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k))
    (held : D B Γ (programGraph L (suc k) ![ctx,ty,q]))
    (left : D B Γ (unary atomicStamp v q)) :
    D B Γ (programGraph (guardedLeast L) (suc k) ![ctx,ty,q]) := by
  have supplied := exact_OpenAtomObserverIntro ctx ty q v left
  have dest := exact_OpenLiteralSelectedObserverOn C E s atomObserver stable ctx ty q k v actual supplied
  exact exact_OpenAtomGuardFromValue L ctx ty q k v held left (exact_OpenAtomObserverElim ctx ty k v dest)

#print axioms exact_OpenAtomOutputFromStamps
#print axioms exact_OpenAtomGuardFromValue
#print axioms exact_OpenAtomGuardOnEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomGuardOnProof
