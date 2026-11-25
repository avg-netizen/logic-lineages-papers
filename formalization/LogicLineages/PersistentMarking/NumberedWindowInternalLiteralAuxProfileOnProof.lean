module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileOnProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralAuxProfileLeastProof
open NumberedWindowInternalLiteralAtomicLeastGuardProof (pairFirst outRaw)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (outReport)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (q k : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![q,k] : Fin 2 → OTerm α) i).relabel j) = ![q.relabel j,k.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun impossible => Fin.elim0 impossible)) i

private theorem pairInput (P : Program 1) (q k value : OTerm α) (src : D B Γ (unary P value q)) :
    D B Γ (programGraph (pairFirst P) value ![q,suc k]) := by
  apply compositionValue P (Fin.cons (.projection 0) Fin.elim0) value ![q,suc k] ![q] src
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![q,suc k]

private theorem coordinateMatch (P : Program 1) (q k value : OTerm α)
    (src : D B Γ (unary P value q)) (dst : D B Γ (unary P value k)) :
    D B Γ (programGraph (matchCoordinates P) (suc z) ![q,suc k]) := by
  let xs : Fin 2 → OTerm α := ![q,suc k]
  have right : D B Γ (programGraph (decodedOutput P) value xs) := by
    apply compositionValue P (Fin.cons outRaw Fin.elim0) value xs ![k] dst
    intro i
    obtain rfl := Fin.eq_zero i
    exact outReport q k
  unfold matchCoordinates
  rw [exact_DispatchControlAST.2.2.2.1]
  apply compositionValue equalityTest (Fin.cons (pairFirst P) (Fin.cons (decodedOutput P) Fin.elim0))
    (suc z) xs (Fin.cons value (Fin.cons value Fin.elim0)) (equalitySelf value)
  exact fun i => Fin.cases (pairInput P q k value src) (Fin.cases right (fun n => Fin.elim0 n)) i

private theorem carryUnary (C : Program 3) (E : Program 4) (s : Settings) (P : Program 1)
    (stable : Preserves E (unaryObserver P)) (ctx ty q k v : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k)) (left : D B Γ (unary P v q)) :
    D B Γ (unary P v k) :=
  exact_OpenUnaryObserverElim P ctx ty k v
    (exact_OpenLiteralSelectedObserverOn C E s (unaryObserver P) stable ctx ty q k v actual
      (exact_OpenUnaryObserverIntro P ctx ty q v left))

private theorem carryMatch (C : Program 3) (E : Program 4) (s : Settings) (P : Program 1)
    (stable : Preserves E (unaryObserver (maskedCoordinate P))) (ctx ty q k event : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k))
    (qShape : D B Γ (unary termShape (suc event) q))
    (kShape : D B Γ (unary termShape (suc event) k)) :
    D B Γ (programGraph (matchCoordinates P) (suc z) ![q,suc k]) := by
  apply programCases P ![q] _
  intro β j Δ v keep src
  simp only [programRename,pairRename,sucRelabel,zRelabel]
  rw [unaryInputsRename] at src
  have old := renameInto actual j Δ keep
  rw [leastOnRename] at old
  have yesA := renameInto qShape j Δ keep
  rw [unaryRename,sucRelabel] at yesA
  have yesB := renameInto kShape j Δ keep
  rw [unaryRename,sucRelabel] at yesB
  let event' := event.relabel j
  let a := q.relabel j
  let b := k.relabel j
  have held := exact_OpenMaskedCoordinateIntro P a event' v yesA src
  have moved := carryUnary C E s (maskedCoordinate P) stable (ctx.relabel j) (ty.relabel j) a b v old held
  have dst := exact_OpenMaskedCoordinateElim P b event' v yesB moved
  exact coordinateMatch P a b v src dst

/-- Every comparison of the original auxiliary profile is now
recreated from the seed and the actual packed minimum's rounds. -/
theorem exact_OpenAuxProfileTestOn (C : Program 3) (E : Program 4) (s : Settings)
    (shapeStable : Preserves E (unaryObserver termShape))
    (leftStable : Preserves E (unaryObserver (maskedCoordinate (field 0))))
    (rightStable : Preserves E (unaryObserver (maskedCoordinate (field 1))))
    (headStable : Preserves E (unaryObserver (maskedCoordinate functionHead)))
    (ctx ty q k : OTerm α) (actual : D B Γ (leastOnGraph C E s ctx ty q k)) :
    D B Γ (programGraph auxProfileTest (suc z) ![q,suc k]) := by
  apply optionGraphCases termShape ![q] _
  · intro β j Δ keep no
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    rw [unaryInputsRename] at no
    have old := renameInto actual j Δ keep
    rw [leastOnRename] at old
    let a := q.relabel j
    let b := k.relabel j
    let xs : Fin 2 → OTerm β := ![a,suc b]
    have target := carryUnary C E s termShape shapeStable (ctx.relabel j) (ty.relabel j) a b z old no
    have shape := coordinateMatch termShape a b z no target
    have fields : D B Δ (programGraph auxFieldsIfPresent (suc z) xs) :=
      zeroBranchIntro (pairFirst termShape) (constantOne 2) fieldMatch (suc z) xs
        (pairInput termShape a b z no) (oneConstantValue xs)
    exact conjunctionAccept (matchCoordinates termShape) auxFieldsIfPresent xs shape fields
  · intro β j Δ event keep yes
    simp only [programRename,pairRename,sucRelabel,zRelabel]
    rw [unaryInputsRename] at yes
    have old := renameInto actual j Δ keep
    rw [leastOnRename] at old
    let c := ctx.relabel j
    let t := ty.relabel j
    let a := q.relabel j
    let b := k.relabel j
    let xs : Fin 2 → OTerm β := ![a,suc b]
    have target := carryUnary C E s termShape shapeStable c t a b (suc event) old yes
    have shape := coordinateMatch termShape a b (suc event) yes target
    have ab := carryMatch C E s (field 0) leftStable c t a b event old yes target
    have cd := carryMatch C E s (field 1) rightStable c t a b event old yes target
    have fn := carryMatch C E s functionHead headStable c t a b event old yes target
    have data : D B Δ (programGraph fieldMatch (suc z) xs) :=
      conjunctionAccept (matchCoordinates (field 0))
        (conjunction (matchCoordinates (field 1)) (matchCoordinates functionHead)) xs ab
        (conjunctionAccept (matchCoordinates (field 1)) (matchCoordinates functionHead) xs cd fn)
    have fields : D B Δ (programGraph auxFieldsIfPresent (suc z) xs) :=
      successorBranchIntro (pairFirst termShape) (constantOne 2) fieldMatch (suc z) event xs
        (pairInput termShape a b (suc event) yes) data
    exact conjunctionAccept (matchCoordinates termShape) auxFieldsIfPresent xs shape fields

theorem exact_OpenAuxProfileFromTest (L : Program 3) (ctx ty q k : OTerm α)
    (actual : D B Γ (programGraph L (suc k) ![ctx,ty,q]))
    (test : D B Γ (programGraph auxProfileTest (suc z) ![q,suc k])) :
    D B Γ (programGraph (auxProfileLeast L) (suc k) ![ctx,ty,q]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let args : Fin 2 → OTerm α := ![q,suc k]
  have keep := successorBranchIntro auxProfileTest (constantZero 2) (.projection 1)
    (suc k) z args test (projectionValue 1 args)
  apply compositionValue retainAuxProfile (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))
    (suc k) xs args keep
  exact fun i => Fin.cases (projectionValue 2 xs) (Fin.cases actual (fun n => Fin.elim0 n)) i

#print axioms exact_OpenAuxProfileTestOn
#print axioms exact_OpenAuxProfileFromTest
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileOnProof
