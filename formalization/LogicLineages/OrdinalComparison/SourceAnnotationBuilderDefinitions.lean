module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataDefinitions
public import LogicLineages.OrdinalComparison.TrackedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder
open ScalarAnnotationData

def repeatTail {k Γ F} (d : Tree k Γ F) : Nat → Tree k Γ F
  | 0 => d
  | n+1 => .add (repeatTail d n) d

def repeatTree {k Γ F} : Nat → Tree k Γ F → Tree k Γ F
  | 0, _ => .free .zero
  | n+1, d => repeatTail d n

/-- Structural source-to-data builder, no choice and no semantic head oracle.
The whole actual vector is retained. Every optional operation is the actual
assignment/abstraction/ground-partial data algorithm. -/
def build {k Γ F n} (e : TrackedSource.Expr k Γ F n) :
    Option (OrdinalVector Γ (Ty.curriedGround n).level × Tree k Γ F) :=
  match e with
  | .tracked => some ((fun j => .var ⟨_,F,j⟩),.tracked)
  | .ground x => some ((fun j => .var ⟨_,x,j⟩),.free (.var ⟨_,x,0⟩))
  | .free t _ => do
      let u ← AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t
      pure (u,.free (u 0))
  | .app f a => do
      let (uf,df) ← build f
      let (ua,da) ← build a
      pure (AdmissibleAssignment.application OrdinalSyntax.defaultPolicy uf ua,
        .collapse ⟨n,TrackedSource.erase f,uf⟩ (.add df da))
  | .lam body => do
      let (ub,db) ← build body
      let u ← AdmissibleAssignment.abstraction OrdinalSyntax.defaultPolicy ub
      let pd ← ScalarAnnotationData.groundPartial db
      let factor := 2^(Ty.ground.level+1)*((List.ofFn ub).map ordinalPartialSize).sum
      pure (u,.add (repeatTree factor pd) (ScalarAnnotationData.closeTree db))

/-- Independent literal scalar traversal of selected collapse heads. Whole
F-free pieces stop, and positive heads are not recursively traversed. -/
def selectedHeads {Γ : List Ty} {σ : Ty} (q : OrdinalExpression (σ :: Γ)) : List (OrdinalExpression (σ :: Γ)) :=
  if ordinalHeadFree q then [] else
  match q with
  | .add a b => selectedHeads a ++ selectedHeads b
  | .collapse h t => h :: selectedHeads t
  | _ => []

def selectedOperators {k Γ} (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here) :
    List (Operator (Ty.curriedGround (k+1) :: Γ)) :=
  if ordinalHeadFree (erase d) then [] else
  match d with
  | .free _ | .tracked => []
  | .add a b => selectedOperators a ++ selectedOperators b
  | .collapse op tail => op :: selectedOperators tail
end LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder
