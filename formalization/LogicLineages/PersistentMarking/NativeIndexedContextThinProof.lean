import LogicLineages.PersistentMarking.NativeIndexedTypingProof
import LogicLineages.PersistentMarking.StructuralContextProof
import LogicLineages.PersistentMarking.TypeSupportConfinementProof

namespace LogicLineages.PersistentMarking.NativeIndexedContextThinProof
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIndexedTypingProof StructuralContext

def eraseContext : SemanticType → Context
  | .base => .hole
  | .arrow a d => .bind (actualType a,0) (eraseContext d)

def kContext (A : SemanticType) (P : Expr) : Context :=
  let η := Ty.arrow (actualType A) (actualType A)
  .head (.app η η) (.cons (left η P) .nil) (eraseContext (.arrow A A)) .nil

def indexedContext (A : SemanticType) (P U : Expr) : Context :=
  let B := actualType A
  let η := Ty.arrow B B
  .head (.app B B) .nil
    (.head (.app (stepType B) η) (.cons (rec1 B zero) .nil) (.bind (.ground,0) (kContext A P)) .nil)
    (.cons U .nil)

theorem eraseTyped (S : Signature) (A : SemanticType) :
    ContextTyped S (eraseContext A) indexType (actualType A) := by
  induction A with
  | base => exact .hole
  | arrow a d _ ih => exact .bind ih

theorem eraseFilled (S : Signature) (A : SemanticType) (i : Expr) (hi : ClosedNative S i indexType) :
    fill (eraseContext A) i = erase A i := by
  induction A with
  | base => rfl
  | arrow a d _ ih =>
    change Expr.lam (actualType a) (close (actualType a,0) (fill (eraseContext d) i)) =
      Expr.lam (actualType a) (erase d i)
    rw [ih,NativeClosedProof.closeClosed (actualType a,0) (erase d i) (erased S d i hi).1.2.2]

theorem kTyped (S : Signature) (A : SemanticType) (P : Expr)
    (hp : ClosedNative S P (.arrow (actualType A) (actualType A))) :
    ContextTyped S (kContext A P) indexType (.arrow (actualType A) (actualType A)) := by
  let η := Ty.arrow (actualType A) (actualType A)
  have hl := leftClosed S η P hp
  exact .head (eraseTyped S (.arrow A A)) ⟨0,rfl⟩ (.cons hl.1.1.1 .nil)
    ⟨hl.1.1.2,True.intro⟩ ⟨hl.1.2.1,True.intro⟩ .nil True.intro True.intro rfl

theorem kFilled (S : Signature) (A : SemanticType) (P i : Expr) (hi : ClosedNative S i indexType) :
    fill (kContext A P) i = K A P i := by
  let η := Ty.arrow (actualType A) (actualType A)
  change app η η (left η P) (fill (eraseContext (.arrow A A)) i) = K A P i
  rw [eraseFilled S (.arrow A A) i hi]
  rfl

theorem contextTyped (S : Signature) (A : SemanticType) (P U : Expr)
    (hp : ClosedNative S P (.arrow (actualType A) (actualType A)))
    (hu : ClosedNative S U (actualType A)) :
    ContextTyped S (indexedContext A P U) indexType (actualType A) := by
  let B := actualType A
  let η := Ty.arrow B B
  have hF : ContextTyped S (.bind (.ground,0) (kContext A P)) indexType (stepType B) :=
    .bind (kTyped S A P hp)
  have hOne := NativeClosedProof.recOne S B
  have hInner : ContextTyped S
      (.head (.app (stepType B) η) (.cons (rec1 B zero) .nil) (.bind (.ground,0) (kContext A P)) .nil)
      indexType η :=
    .head hF ⟨0,rfl⟩ (.cons hOne.1.1.1 .nil)
      ⟨hOne.1.1.2,True.intro⟩ ⟨hOne.1.2.1,True.intro⟩ .nil True.intro True.intro rfl
  exact .head hInner ⟨0,rfl⟩ .nil True.intro True.intro (.cons hu.1.1.1 .nil)
    ⟨hu.1.1.2,True.intro⟩ ⟨hu.1.2.1,True.intro⟩ rfl

theorem contextFilled (S : Signature) (A : SemanticType) (P U i : Expr)
    (hp : ClosedNative S P (.arrow (actualType A) (actualType A))) (hi : ClosedNative S i indexType) :
    fill (indexedContext A P U) i = indexedW A P U i := by
  let B := actualType A
  change recTerm B zero (.lam .ground (close (.ground,0) (fill (kContext A P) i))) U = _
  rw [kFilled S A P i hi,NativeClosedProof.closeClosed (.ground,0) (K A P i) (kClosed S A P i hp hi).1.2.2]
  rfl

theorem contextStrict (S : Signature) (A : SemanticType) (P U i j : Expr)
    (hp : ClosedNative S P (.arrow (actualType A) (actualType A)))
    (hu : ClosedNative S U (actualType A)) (hi : ClosedNative S i indexType) (hj : ClosedNative S j indexType)
    (h : ConfinedPair.Strict S i j) :
    ConfinedPair.Strict S (indexedW A P U i) (indexedW A P U j) := by
  let C := indexedContext A P U
  let B := actualType A
  have hc := contextTyped S A P U hp hu
  have hs := hi.1.1
  have ht := hj.1.1
  have ho := hi.1.2.1
  have hO := hj.1.2.1
  have hEdge : ConfinedPair.Strict S (fill C i) (fill C j) :=
    ⟨⟨B,StructuralFillProof.fillPaper S C indexType B i hc hs,StructuralFillProof.fillPaper S C indexType B j hc ht,
      StructuralFillProof.fillOrdinary S C indexType B i hc ho,StructuralFillProof.fillOrdinary S C indexType B j hc hO⟩,
      StructuralContextProof.strictContext S C indexType B i j hc hs ht ho hO h.2.1,
      TypeSupportConfinementProof.contextConfinement S C indexType B i j hc hs ht ho hO h.2.2⟩
  change ConfinedPair.Strict S (fill (indexedContext A P U) i) (fill (indexedContext A P U) j) at hEdge
  rw [contextFilled S A P U i hp hi,contextFilled S A P U j hp hj] at hEdge
  exact hEdge

end LogicLineages.PersistentMarking.NativeIndexedContextThinProof
