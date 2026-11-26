module

public import LogicLineages.NativeModule.PersistentMarking.NativeCarrierTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIndexedCarrierTargets
open Spine NativeReduction NativeCarrierTargets

inductive SemanticType where
  | base
  | arrow : SemanticType → SemanticType → SemanticType

def indexType : Ty := .arrow .ground .ground

def actualType : SemanticType → Ty
  | .base => indexType
  | .arrow a d => .arrow (actualType a) (actualType d)

def erase : SemanticType → Expr → Expr
  | .base, i => i
  | .arrow a d, i => .lam (actualType a) (erase d i)

def discard (η : Ty) : Expr := .lam η (.lam η (.bound η 1))

def left (η : Ty) (P : Expr) : Expr := app η (.arrow η η) (discard η) P

def K (A : SemanticType) (P i : Expr) : Expr :=
  let B := actualType A
  let η := Ty.arrow B B
  app η η (left η P) (erase (.arrow A A) i)

def indexedW (A : SemanticType) (P U i : Expr) : Expr := W (actualType A) (K A P i) U

def IndexedCarrier : Prop := ∀ S A P U i,
  ClosedNative S P (.arrow (actualType A) (actualType A)) →
  ClosedNative S U (actualType A) → ClosedNative S i indexType →
  ConfinedPair.Strict S (indexedW A P U i) U ∧
  ∀ j, ClosedNative S j indexType → ConfinedPair.Strict S i j →
    ConfinedPair.Strict S (indexedW A P U i) (indexedW A P U j) ∧
    ConfinedPair.Strict S (indexedW A P U i) (app (actualType A) (actualType A) P (indexedW A P U j))

end LogicLineages.PersistentMarking.NativeIndexedCarrierTargets
