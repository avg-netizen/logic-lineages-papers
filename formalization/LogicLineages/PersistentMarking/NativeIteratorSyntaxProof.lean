import LogicLineages.PersistentMarking.NativeIteratorTargets
import LogicLineages.PersistentMarking.NativeIndexedTypingThinProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.NativeIteratorSyntaxProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets

private theorem appTyped {C σ τ q u} (hq : Typed C q (.arrow σ τ)) (hu : Typed C u σ) :
    Typed C (app σ τ q u) τ :=
  .head (.cons hq (.cons hu .nil))

private theorem eraseTyped (A : SemanticType) (C : BoundContext) (i : Nat) (hi : C i = some indexType) :
    Typed C (eraseBound A i) (actualType A) := by
  induction A generalizing C i with
  | base => exact .bound hi
  | arrow a d _ ih => exact .lam (ih (C.push (actualType a)) (i + 1) hi)

theorem bodyTyped (A : SemanticType) :
    Typed (((EmptyContext.push indexType).push (functionType A)).push (actualType A))
      (iteratorBody A) (actualType A) := by
  let B := actualType A
  let η := functionType A
  let C := ((EmptyContext.push indexType).push η).push B
  let openContext := C.push .ground
  have hP : Typed openContext (.bound η 2) η := .bound rfl
  have hDiscard : Typed openContext (NativeIndexedCarrierTargets.discard η) (.arrow η (.arrow η η)) :=
    .lam (.lam (.bound rfl))
  have hErase : Typed openContext (eraseBound (.arrow A A) 3) η := eraseTyped (.arrow A A) openContext 3 rfl
  have hStep : Typed C (.lam .ground (app η η (left η (.bound η 2)) (eraseBound (.arrow A A) 3))) (stepType B) :=
    .lam (appTyped (appTyped hDiscard hP) hErase)
  have hRec : Typed C (rec1 B zero) (.arrow (stepType B) η) := appTyped (.head .nil) (.head .nil)
  exact appTyped (appTyped hRec hStep) (.bound rfl)

private theorem eraseShape (S : Signature) (A : SemanticType) (i : Nat) :
    Valid S (eraseBound A i) ∧ Ordinary (eraseBound A i) ∧ Closed (eraseBound A i) ∧
      DecisionInventory.heads (eraseBound A i) = [] := by
  induction A generalizing i with
  | base => exact ⟨True.intro, True.intro, fun _ => rfl, rfl⟩
  | arrow a d _ ih => exact ih (i + 1)

theorem closed : ClosedNativeIterator := by
  intro S A
  obtain ⟨hValid, hOrdinary, hClosed, hHeads⟩ := eraseShape S (.arrow A A) 3
  refine ⟨⟨⟨.lam (.lam (.lam (bodyTyped A))), ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [iterator, iteratorBody, recTerm, rec2, rec1, zero, app, left, NativeIndexedCarrierTargets.discard,
      Valid, ValidArgs, Admitted, classRank, hValid]
  · simp [iterator, iteratorBody, recTerm, rec2, rec1, zero, app, left, NativeIndexedCarrierTargets.discard,
      Ordinary, OrdinaryArgs, hOrdinary]
  · intro name
    simp [iterator, iteratorBody, recTerm, rec2, rec1, zero, app, left, NativeIndexedCarrierTargets.discard,
      NameBridge.freeOccurs, NameBridge.freeOccursArgs, hClosed name]
  · intro name arity
    simp [iterator, iteratorBody, recTerm, rec2, rec1, zero, app, left, NativeIndexedCarrierTargets.discard,
      DecisionInventory.heads, DecisionInventory.headsArgs, hHeads]

private theorem eraseSubstitute (A : SemanticType) (i p u : Expr) (d : Nat)
    (hi : Typed EmptyContext i indexType) :
    substitute (.cons u (.cons p (.cons i .nil))) d (eraseBound A (d + 2)) = erase A i := by
  induction A generalizing d with
  | base =>
    have hBelow : ¬ d + 2 < d := by omega
    have hIndex : d + 2 - d = 2 := by omega
    simpa only [eraseBound, erase, substitute, hBelow, if_false, hIndex, Args.get] using
      ClosedSyntaxProof.closedShift i indexType hi d
  | arrow a body _ ih =>
    have hIndex : d + 2 + 1 = (d + 1) + 2 := by omega
    simp only [eraseBound, erase, substitute, hIndex, ih]

theorem literal : IteratorLiteralInstantiation := by
  intro S A i p u hi hp hu
  let B := actualType A
  let η := functionType A
  let values : Args := .cons u (.cons p (.cons i .nil))
  have hErase : substitute values 1 (eraseBound (.arrow A A) 3) = erase (.arrow A A) i :=
    eraseSubstitute (.arrow A A) i p u 1 hi.1.1.1
  have hParameter : substitute values 1 (.bound η 2) = p :=
    ClosedSyntaxProof.closedShift p η hp.1.1.1 1
  have hInput : substitute values 0 (.bound B 0) = u :=
    ClosedSyntaxProof.closedShift u B hu.1.1.1 0
  change recTerm B zero
    (.lam .ground (app η η (app η (.arrow η η) (NativeIndexedCarrierTargets.discard η)
      (substitute values 1 (.bound η 2)))
      (substitute values 1 (eraseBound (.arrow A A) 3))))
    (substitute values 0 (.bound B 0)) = indexedW A p u i
  rw [hParameter, hErase, hInput]
  rfl

end LogicLineages.PersistentMarking.NativeIteratorSyntaxProof
