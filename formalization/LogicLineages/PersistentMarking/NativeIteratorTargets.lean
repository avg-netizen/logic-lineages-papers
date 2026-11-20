import LogicLineages.PersistentMarking.NativeIndexedCarrierTargets

namespace LogicLineages.PersistentMarking.NativeIteratorTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets

/-- Terminal-index erasure with the live de Bruijn index carried under
every new lambda. The old `erase` takes a closed term instead. -/
def eraseBound : SemanticType → Nat → Expr
  | .base, index => .bound indexType index
  | .arrow a d, index => .lam (actualType a) (eraseBound d (index + 1))

def functionType (A : SemanticType) : Ty := .arrow (actualType A) (actualType A)

def iteratorType (A : SemanticType) : Ty :=
  .arrow indexType (.arrow (functionType A) (functionType A))

/-- The manuscript's iterator body. Outside the recursor step lambda,
the indices of u, p and i are 0, 1 and 2. The occurrence of p inside
that lambda has index 2, and erasure starts at index 3 for i. -/
def iteratorBody (A : SemanticType) : Expr :=
  let B := actualType A
  let η := functionType A
  recTerm B zero (.lam .ground (app η η (left η (.bound η 2)) (eraseBound (.arrow A A) 3))) (.bound B 0)

def iterator (A : SemanticType) : Expr :=
  .lam indexType (.lam (functionType A) (.lam (actualType A) (iteratorBody A)))

def applied (A : SemanticType) (i p u : Expr) : Expr :=
  let B := actualType A
  let η := functionType A
  app B B (app η η (app indexType (.arrow η η) (iterator A) i) p) u

def afterIndexBody (A : SemanticType) (i : Expr) : Expr :=
  substitute (.cons i .nil) 2 (iteratorBody A)

def afterFunctionBody (A : SemanticType) (i p : Expr) : Expr :=
  substitute (.cons p .nil) 1 (afterIndexBody A i)

def afterIndex (A : SemanticType) (i p u : Expr) : Expr :=
  let B := actualType A
  let η := functionType A
  app B B (app η η (.lam η (.lam B (afterIndexBody A i))) p) u

def afterFunction (A : SemanticType) (i p u : Expr) : Expr :=
  let B := actualType A
  app B B (.lam B (afterFunctionBody A i p)) u

def ClosedNativeIterator : Prop :=
  ∀ S A, ClosedNative S (iterator A) (iteratorType A)

def IteratorLiteralInstantiation : Prop :=
  ∀ S A i p u, ClosedNative S i indexType → ClosedNative S p (functionType A) →
    ClosedNative S u (actualType A) →
    substitute (.cons u (.cons p (.cons i .nil))) 0 (iteratorBody A) = indexedW A p u i

def IteratorNativeBetaTransport : Prop :=
  ∀ S A i p u, ClosedNative S i indexType → ClosedNative S p (functionType A) →
    ClosedNative S u (actualType A) →
    Reduction S (applied A i p u) (afterIndex A i p u) ∧
      Reduction S (afterIndex A i p u) (afterFunction A i p u) ∧
      Reduction S (afterFunction A i p u) (indexedW A p u i)

end LogicLineages.PersistentMarking.NativeIteratorTargets
