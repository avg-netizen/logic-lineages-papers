module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassObserverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
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

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassGuardOnProof
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

open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralClassObserverProof
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- If the actual two auxiliary queries share a selected output, then
both child class queries can transport their literal values between
the two original raw inputs through that exact common output. -/
private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem compareActual (p : Program 2) (n q r v : OTerm α)
    (left : D B Γ (programGraph p v ![n,q]))
    (right : D B Γ (programGraph p v ![n,r])) :
    D B Γ (programGraph (compareChildClass p) (suc z) ![n,q,suc r]) := by
  let xs : Fin 3 → OTerm α := ![n,q,suc r]
  have x : D B Γ (programGraph (onSource p) v xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))
      v xs ![n,q] left
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs) (fun e => Fin.elim0 e)) i
  have raw : D B Γ (programGraph resultRaw r xs) := by
    unfold resultRaw
    rw [exact_DispatchControlAST.2.2.1]
    apply compositionValue predecessor (Fin.cons (.projection 2) Fin.elim0) r xs ![suc r]
      (predecessorSuccessor r)
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  have y : D B Γ (programGraph (onResult p) v xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons resultRaw Fin.elim0)) v xs ![n,r] right
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases raw (fun e => Fin.elim0 e)) i
  unfold compareChildClass
  rw [exact_DispatchControlAST.2.2.2.1]
  apply compositionValue equalityTest (Fin.cons (onSource p) (Fin.cons (onResult p) Fin.elim0))
    (suc z) xs (Fin.cons v (Fin.cons v Fin.elim0)) (equalitySelf v)
  exact fun i => Fin.cases x (Fin.cases y (fun e => Fin.elim0 e)) i

private theorem carry (C : Program 3) (E : Program 4) (s : Settings) (P : Program 2)
    (stable : Preserves E (classObserver P)) (ctx ty q k ev : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k))
    (atQ : D B Γ (unary termShape (suc ev) q)) (atK : D B Γ (unary termShape (suc ev) k)) :
    D B Γ (programGraph (compareChildClass P) (suc z) ![ctx,q,suc k]) := by
  apply programCases P ![ctx,q] _
  intro β j Δ v keep source
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
  rw [pairRename] at source
  have qShape := renameInto atQ j Δ keep
  rw [unaryRename,sucRelabel] at qShape
  have kShape := renameInto atK j Δ keep
  rw [unaryRename,sucRelabel] at kShape
  have run := renameInto actual j Δ keep
  rw [leastOnRename] at run
  let c := ctx.relabel j
  let t := ty.relabel j
  let a := q.relabel j
  let b := k.relabel j
  let e := ev.relabel j
  have obs := exact_OpenActiveClassObserverIntro P c t a e v qShape source
  have dest := exact_OpenLiteralSelectedObserverOn C E s (classObserver P) stable c t a b v run obs
  exact compareActual P c a b v source (exact_OpenActiveClassObserverElim P c t b e v kShape dest)

private theorem checkerShape (ctx q k value : OTerm α)
    (shape : D B Γ (unary termShape value q)) :
    D B Γ (programGraph selectedAuxiliary value ![ctx,q,suc k]) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc k]
  apply compositionValue termShape (Fin.cons (.projection 1) Fin.elim0) value xs ![q] shape
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 xs

/-- Actual function and argument values of the separately named
comparator survive the actual enriched rounds and pay the two
open comparisons. The theorem does not equate this comparator with
the program producing the selected result. -/
theorem exact_OpenClassCheckOn (C : Program 3) (E : Program 4) (s : Settings) (K : Program 3)
    (shape : Preserves E (unaryObserver termShape))
    (fn : Preserves E (classObserver (functionClass K)))
    (arg : Preserves E (classObserver (argumentClass K)))
    (ctx ty q k : OTerm α) (actual : D B Γ (leastOnGraph C E s ctx ty q k)) :
    D B Γ (programGraph (checkAuxiliaryClasses K) (suc z) ![ctx,q,suc k]) := by
  apply optionGraphCases termShape ![q] _
  · intro β j Δ keep no
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    rw [unaryInputsRename] at no
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,q.relabel j,suc (k.relabel j)]
    exact zeroBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree K)
      (suc z) xs (checkerShape (ctx.relabel j) (q.relabel j) (k.relabel j) z no) (oneConstantValue xs)
  · intro β j Δ ev keep active
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    rw [unaryInputsRename] at active
    have accepted := renameInto actual j Δ keep
    rw [leastOnRename] at accepted
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := k.relabel j
    let xs : Fin 3 → OTerm β := ![c,a,suc b]
    have observeQ := exact_OpenUnaryObserverIntro termShape c t a (suc ev) active
    have observeK := exact_OpenLiteralSelectedObserverOn C E s (unaryObserver termShape) shape c t a b
      (suc ev) accepted observeQ
    have kShape := exact_OpenUnaryObserverElim termShape c t b (suc ev) observeK
    have first := carry C E s (functionClass K) fn c t a b ev accepted active kShape
    have second := carry C E s (argumentClass K) arg c t a b ev accepted active kShape
    exact successorBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree K)
      (suc z) ev xs (checkerShape c a b (suc ev) active)
      (conjunctionAccept (compareChildClass (functionClass K)) (compareChildClass (argumentClass K)) xs first second)

/-- A distinct producer is deliberate: installation must never create
a self-referential Program AST. This specializes definitionally to the
original constructor when its two slots use the same program. -/
def classGuardWith (K L : Program 3) : Program 3 :=
  .composition (retainClasses K) (Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)))

theorem exact_ClassGuardWithDiagonal (L : Program 3) : classGuardWith L L = auxClassLeast L := rfl

theorem exact_OpenClassGuardWithIntro (K L : Program 3) (ctx ty q k : OTerm α)
    (produced : D B Γ (programGraph L (suc k) ![ctx,ty,q]))
    (paid : D B Γ (programGraph (checkAuxiliaryClasses K) (suc z) ![ctx,q,suc k])) :
    D B Γ (programGraph (classGuardWith K L) (suc k) ![ctx,ty,q]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let args : Fin 3 → OTerm α := ![ctx,q,suc k]
  have kept := successorBranchIntro (checkAuxiliaryClasses K) (constantZero 3) (.projection 2)
    (suc k) z args paid (projectionValue 2 args)
  apply compositionValue (retainClasses K) (Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)))
    (suc k) xs args kept
  exact fun i => Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases produced (fun n => Fin.elim0 n))) i

#print axioms exact_OpenClassCheckOn
#print axioms exact_ClassGuardWithDiagonal
#print axioms exact_OpenClassGuardWithIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassGuardOnProof
