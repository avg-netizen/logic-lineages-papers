module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngleDefinitions

@[expose] public section
/-! A constructive codec for the ACTUAL original Source.Term syntax. Original
application is the ordinary functional head, and ranked arguments are genuine
Fin-indexed source terms. Auxiliary app/bottom/numbered nodes are rejected.
This source presentation uses the existing auxiliary packed number unchanged;
it neither changes original syntax nor asserts computability by definition.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodec
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedOriginalAngle

inductive OriginalArguments (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) : List Ty → Type where
  | nil : OriginalArguments Symbol arity Gamma []
  | cons {sigma types} : Term Symbol arity Gamma sigma → OriginalArguments Symbol arity Gamma types →
      OriginalArguments Symbol arity Gamma (sigma::types)

def groundValues {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    (k : Nat) → OriginalArguments Symbol arity Gamma (List.replicate k .ground) → Fin k → Term Symbol arity Gamma .ground
  | 0,.nil => Fin.elim0
  | k+1,.cons q rest => Fin.cases q (groundValues k rest)

def groundArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    (k : Nat) → (Fin k → Term Symbol arity Gamma .ground) → OriginalArguments Symbol arity Gamma (List.replicate k .ground)
  | 0,_ => .nil
  | k+1,f => .cons (f 0) (groundArguments k (fun i => f i.succ))

def translateArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} :
    OriginalArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types
  | .nil => .nil
  | .cons q rest => .cons (translateOriginal q) (translateArguments rest)

mutual
def project {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Option (Term Symbol arity Gamma tau)
  | .var v => some (.var v)
  | .lam body => (project body).map Term.lam
  | .app _ _ | .bottom _ | .numbered _ _ _ _ _ _ => none
  | .ordinary .zero _ => some .zeroC
  | .ordinary .succ _ => some .succC
  | .ordinary (.cases tau) _ => some (.caseC tau)
  | .ordinary (.recursor tau) _ => some (.recC tau)
  | .ordinary (.application sigma tau) base => do
    let values ← projectArguments base
    match values with
    | .cons f (.cons a .nil) => pure (.app f a)
  | .ordinary (.ranked f) base => do
    let values ← projectArguments base
    pure (.ranked f (groundValues (arity f) values))
def projectArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} :
    AuxArguments Symbol arity Gamma types → Option (OriginalArguments Symbol arity Gamma types)
  | .nil => some .nil
  | .cons q rest => do
    let q' ← project q
    let rest' ← projectArguments rest
    pure (.cons q' rest')
end

def sourceNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (s : Term (Fin n) arity Gamma tau) : Nat := packedNumber ⟨tau,translateOriginal s⟩

def decodeSourceNumber (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (value : Nat) :
    Option (Term (Fin n) arity Gamma tau) := do
  let q ← decodePackedNumber n arity Gamma value
  if h : q.1=tau then project (transportAux h q.2) else none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodec
