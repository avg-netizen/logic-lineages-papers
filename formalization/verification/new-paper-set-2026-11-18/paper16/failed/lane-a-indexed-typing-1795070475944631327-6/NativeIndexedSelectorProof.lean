import LogicLineages.PersistentMarking.NativeIndexedTypingProof

namespace LogicLineages.PersistentMarking.NativeIndexedSelectorProof
open Spine NativeReduction NativeTypingProof NativeCarrierTargets
open NativeIndexedCarrierTargets NativeIndexedTypingProof

private def outerBase (A : SemanticType) (P i : Expr) : Args :=
  let η := Ty.arrow (actualType A) (actualType A)
  .cons (left η P) (.cons (erase (.arrow A A) i) .nil)

private def outer (A : SemanticType) (P i : Expr) : Expr :=
  let η := Ty.arrow (actualType A) (actualType A)
  .marked (.app η η) η (outerBase A P i) .nil

private def inner (A : SemanticType) (P i : Expr) : Expr :=
  let η := Ty.arrow (actualType A) (actualType A)
  .marked (.app η (.arrow η η)) η (.cons (discard η) (.cons P .nil)) (.cons (outer A P i) .nil)

private theorem selectCall (A : SemanticType) (P i : Expr) :
    let η := Ty.arrow (actualType A) (actualType A)
    apply (left η P) (ownerCopies (.app η η) (outerBase A P i) .nil [η]) = some (inner A P i) := by
  simp [left,app,apply,applyAux,consumeTypes,Head.result,ownerCopies,Expr.type,inner,outer,
    SubstitutionProof.emptyArgsSubstitution]

/-- Select exactly the literal inner application, appending one same-owner
copy, then select its original second base occurrence by the empty call. -/
theorem selectP (S : Signature) (A : SemanticType) (P i : Expr)
    (hP : ClosedNative S P (.arrow (actualType A) (actualType A))) (hi : ClosedNative S i indexType) :
    ConfinedPair.Strict S (K A P i) P := by
  let η := Ty.arrow (actualType A) (actualType A)
  let e := erase (.arrow A A) i
  have hLeft := leftClosed S η P hP
  have he := erased S (.arrow A A) i hi
  have hOuter : PaperTerm S (outer A P i) η :=
    markedAppPaper S η η η (left η P) e .nil hLeft.1.1 he.1.1 .nil True.intro
  have hInner : Weak S (inner A P i) P :=
    secondSelect S η (.arrow η η) (discard η) P (.cons (outer A P i) .nil)
      (discardClosed S η).1.1 hP.1.1 hP.1.2.1 (.cons hOuter.1 .nil) ⟨hOuter.2,True.intro⟩
  have hw : Weak S (outer A P i) P :=
    .select (domains := [η]) hOuter hP.1.1 (Or.inl .here) hLeft.1.1.1 (selectCall A P i) hInner
  have hK := kClosed S A P i hP hi
  exact ⟨⟨η,hK.1.1,hP.1.1,hK.1.2.1,hP.1.2.1⟩,
    .intro hK.1.1 hP.1.1 rfl hw,supportP A P i⟩

end LogicLineages.PersistentMarking.NativeIndexedSelectorProof
