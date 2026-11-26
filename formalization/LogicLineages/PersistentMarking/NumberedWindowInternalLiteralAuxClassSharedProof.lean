module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassReadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassSharedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalEqualityTest (equalityTest predecessor)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAuxClassLeastProof
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassTests)
open NumberedWindowInternalLiteralAuxClassReadProof (exact_OpenChildClassTransfer)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- If the actual two auxiliary queries share a selected output, then
both child class queries can transport their literal values between
the two original raw inputs through that exact common output. -/
theorem exact_OpenSharedAuxChildClasses (L : Program 3) (ctx ty q r k a b : OTerm α)
    (l : D B Γ (programGraph (auxClassLeast L) (suc k) ![ctx,ty,q]))
    (m : D B Γ (programGraph (auxClassLeast L) (suc k) ![ctx,ty,r]))
    (sq : D B Γ (unary termShape (suc z) q)) (sr : D B Γ (unary termShape (suc z) r)) :
    (D B Γ (programGraph (functionClass L) a ![ctx,q]) →
      D B Γ (programGraph (functionClass L) a ![ctx,r])) ∧
    (D B Γ (programGraph (argumentClass L) b ![ctx,q]) →
      D B Γ (programGraph (argumentClass L) b ![ctx,r])) := by
  obtain ⟨one⟩ := exact_OpenLiteralAuxClassTests L ctx ty q k l sq
  obtain ⟨two⟩ := exact_OpenLiteralAuxClassTests L ctx ty r k m sr
  let funQ := exact_OpenChildClassTransfer (functionClass L) ctx q k a ⟨Derivation.conjunctionLeft one⟩
  let funR := exact_OpenChildClassTransfer (functionClass L) ctx r k a ⟨Derivation.conjunctionLeft two⟩
  let argQ := exact_OpenChildClassTransfer (argumentClass L) ctx q k b ⟨Derivation.conjunctionRight one⟩
  let argR := exact_OpenChildClassTransfer (argumentClass L) ctx r k b ⟨Derivation.conjunctionRight two⟩
  exact ⟨funR.2 ∘ funQ.1,argR.2 ∘ argQ.1⟩

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem compareSelf (p : Program 2) (ctx q : OTerm α) :
    D B Γ (programGraph (compareChildClass p) (suc z) ![ctx,q,suc q]) := by
  apply programCases p ![ctx,q] _
  intro β j Δ v keep got
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
  rw [pairRename] at got
  let n := ctx.relabel j
  let r := q.relabel j
  let xs : Fin 3 → OTerm β := ![n,r,suc r]
  have x : D B Δ (programGraph (onSource p) v xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))
      v xs ![n,r] got
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs) (fun e => Fin.elim0 e)) i
  have raw : D B Δ (programGraph resultRaw r xs) := by
    unfold resultRaw
    rw [exact_DispatchControlAST.2.2.1]
    apply compositionValue predecessor (Fin.cons (.projection 2) Fin.elim0) r xs ![suc r]
      (predecessorSuccessor r)
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  have y : D B Δ (programGraph (onResult p) v xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons resultRaw Fin.elim0)) v xs ![n,r] got
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases raw (fun e => Fin.elim0 e)) i
  unfold compareChildClass
  rw [exact_DispatchControlAST.2.2.2.1]
  apply compositionValue equalityTest (Fin.cons (onSource p) (Fin.cons (onResult p) Fin.elim0))
    (suc z) xs (Fin.cons v (Fin.cons v Fin.elim0)) (equalitySelf v)
  exact fun i => Fin.cases x (Fin.cases y (fun e => Fin.elim0 e)) i

private theorem checkSelf (L : Program 3) (ctx q : OTerm α) :
    D B Γ (programGraph (checkAuxiliaryClasses L) (suc z) ![ctx,q,suc q]) := by
  apply optionGraphCases selectedAuxiliary ![ctx,q,suc q] _
  · intro β j Δ keep absent
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    simp only [tripleInputsRename,sucRelabel] at absent
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,q.relabel j,suc (q.relabel j)]
    exact zeroBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree L)
      (suc z) xs absent (oneConstantValue xs)
  · intro β j Δ p keep accepted
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    simp only [tripleInputsRename,sucRelabel] at accepted
    let n := ctx.relabel j
    let r := q.relabel j
    let xs : Fin 3 → OTerm β := ![n,r,suc r]
    have both : D B Δ (programGraph (childClassesAgree L) (suc z) xs) :=
      conjunctionAccept (compareChildClass (functionClass L)) (compareChildClass (argumentClass L)) xs
        (compareSelf (functionClass L) n r) (compareSelf (argumentClass L) n r)
    exact successorBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree L) (suc z) p xs
      accepted both

theorem exact_OpenLiteralAuxClassSelfLeast (L : Program 3) (ctx ty q : OTerm α)
    (held : D B Γ (programGraph L (suc q) ![ctx,ty,q])) :
    D B Γ (programGraph (auxClassLeast L) (suc q) ![ctx,ty,q]) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc q]
  have test : D B Γ (programGraph (checkAuxiliaryClasses L) (suc z) xs) := checkSelf L ctx q
  have kept := successorBranchIntro (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)
    (suc q) z xs test (projectionValue 2 xs)
  apply compositionValue (retainClasses L) (Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)))
    (suc q) ![ctx,ty,q] xs kept
  exact fun i => Fin.cases (projectionValue 0 ![ctx,ty,q])
    (Fin.cases (projectionValue 2 ![ctx,ty,q]) (Fin.cases held (fun e => Fin.elim0 e))) i

#print axioms exact_OpenSharedAuxChildClasses
#print axioms exact_OpenLiteralAuxClassSelfLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassSharedProof
