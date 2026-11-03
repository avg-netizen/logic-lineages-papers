module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdges
open Source NativeCarrier NativeRecursor

abbrev indexType : Ty := .arrow .ground .ground

def translatedType : Ty → Ty
  | .ground => indexType
  | .arrow A D => .arrow (translatedType A) (translatedType D)

def constantTemplate {Symbol : Type} {arity : Symbol → Nat} (A : Ty)
    {Γ : List Ty} (i : Term Symbol arity Γ indexType) : Term Symbol arity Γ (translatedType A) :=
  match A with
  | .ground => i
  | .arrow A D => .lam (constantTemplate D (i.rename (Renaming.weaken Γ (translatedType A))))

def selector {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} (η : Ty) :
    Term Symbol arity Γ (.arrow η (.arrow η η)) := .lam (.lam (.var (.there .here)))

def step {Symbol : Type} {arity : Symbol → Nat} (A : Ty)
    (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (i : Term Symbol arity [] indexType) : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)) :=
  .app (.app (selector (.arrow (translatedType A) (translatedType A))) P) (constantTemplate (.arrow A A) i)

def iterationCarrier {Symbol : Type} {arity : Symbol → Nat} (A : Ty)
    (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (U : Term Symbol arity [] (translatedType A)) (i : Term Symbol arity [] indexType) : Term Symbol arity [] (translatedType A) :=
  carrier (step A P i) U

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdges
