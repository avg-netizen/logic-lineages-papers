module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (sameHeader allowedOutput headerLeast inputHead outputHead)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (checkSame checkAtom keepAtom atomOutput guardedLeast outRaw)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D outReport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (x y : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![x,y] : Fin 2 → OTerm α) i).relabel j) = ![x.relabel j,y.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem keepSelf (k : OTerm α) : D B Γ (programGraph keepAtom (suc k) ![k,suc k]) := by
  let xs : Fin 2 → OTerm α := ![k,suc k]
  have cmp : D B Γ (programGraph checkSame (suc z) xs) := by
    unfold checkSame
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest (Fin.cons (.projection 0) (Fin.cons outRaw Fin.elim0))
      (suc z) xs (Fin.cons k (Fin.cons k Fin.elim0)) (equalitySelf k)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (outReport k k) (fun e => Fin.elim0 e)) i
  exact successorBranchIntro checkSame (constantZero 2) (.projection 1) (suc k) z xs cmp
    (projectionValue 1 xs)

private theorem atomSelf (k : OTerm α) : D B Γ (programGraph atomOutput (suc k) ![k,suc k]) := by
  let xs : Fin 2 → OTerm α := ![k,suc k]
  apply optionGraphCases checkAtom xs (programGraph atomOutput (suc k) xs)
  · intro β j Δ _ no
    simp only [xs,programRename,pairRename,sucRelabel]
    simp only [xs,pairRename,sucRelabel] at no
    let tape : Fin 2 → OTerm β := ![k.relabel j,suc (k.relabel j)]
    exact zeroBranchIntro checkAtom (.projection 1) keepAtom (suc (k.relabel j)) tape no
      (projectionValue 1 tape)
  · intro β j Δ pred _ yes
    simp only [xs,programRename,pairRename,sucRelabel]
    simp only [xs,pairRename,sucRelabel] at yes
    exact successorBranchIntro checkAtom (.projection 1) keepAtom (suc (k.relabel j)) pred
      ![k.relabel j,suc (k.relabel j)] yes (keepSelf (k.relabel j))

private theorem headerSelf (k : OTerm α) : D B Γ (programGraph allowedOutput (suc k) ![k,suc k]) := by
  apply programCases cellHead ![k] (programGraph allowedOutput (suc k) ![k,suc k])
  intro β j Δ h _ head
  simp only [programRename,pairRename,sucRelabel]
  rw [inputsRename] at head
  let a := k.relabel j
  let xs : Fin 2 → OTerm β := ![a,suc a]
  have in' : D B Δ (programGraph inputHead h xs) := by
    apply compositionValue cellHead (Fin.cons (.projection 0) Fin.elim0) h xs ![a] head
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have out' : D B Δ (programGraph outputHead h xs) := by
    apply compositionValue cellHead (Fin.cons outRaw Fin.elim0) h xs ![a] head
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport a a
  have cmp : D B Δ (programGraph sameHeader (suc z) xs) := by
    unfold sameHeader
    rw [exact_DispatchControlAST.2.2.2.1]
    apply compositionValue equalityTest (Fin.cons inputHead (Fin.cons outputHead Fin.elim0))
      (suc z) xs (Fin.cons h (Fin.cons h Fin.elim0)) (equalitySelf h)
    intro i
    exact Fin.cases in' (Fin.cases out' (fun e => Fin.elim0 e)) i
  exact successorBranchIntro sameHeader (constantZero 2) (.projection 1) (suc a) z xs cmp
    (projectionValue 1 xs)

/-- Reconstruct the actual installed double-guarded self-least from
the old successful self-least by the two literal reflexive comparisons.
The new graphs are built, not inferred from numerical calibration. -/
theorem exact_OpenLiteralGuardedSelfLeast (L : Program 3) (ctx ty k : OTerm α)
    (h : D B Γ (programGraph L (suc k) ![ctx,ty,k])) :
    D B Γ (programGraph (guardedLeast (headerLeast L)) (suc k) ![ctx,ty,k]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,k]
  let args : Fin 2 → OTerm α := ![k,suc k]
  have hd : D B Γ (programGraph (headerLeast L) (suc k) xs) := by
    apply compositionValue allowedOutput (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))
      (suc k) xs args (headerSelf k)
    intro i
    exact Fin.cases (projectionValue 2 xs) (Fin.cases h (fun e => Fin.elim0 e)) i
  apply compositionValue atomOutput (Fin.cons (.projection 2) (Fin.cons (headerLeast L) Fin.elim0))
    (suc k) xs args (atomSelf k)
  intro i
  exact Fin.cases (projectionValue 2 xs) (Fin.cases hd (fun e => Fin.elim0 e)) i

#print axioms exact_OpenLiteralGuardedSelfLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralGuardedSelfLeastProof
