module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions
public import Mathlib.Data.List.Perm.Basic

@[expose] public section
/-! Raw, typed all-Mul numbered auxiliary reduction from source06/ Kop5.3.
This is NOT a new source comparison. In particular auxiliary app has ONLY
function-side monotonicity; an original functional @ head remains an ordinary
head with its actual typed base. Equivalence quotienting, finite-S confinement,
numeric coding, arithmetic accessibility and full simulation remain separate.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteReduction
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax

abbrev Packed (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :=
  Sigma (AuxTerm Symbol arity Gamma)

def argumentList {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} :
    AuxArguments Symbol arity Gamma types → List (Packed Symbol arity Gamma)
  | .nil => []
  | .cons q rest => ⟨_,q⟩::argumentList rest

/-- Ordinary label omega can be marked once to ANY finite n; an already
numbered head is not marked again by this primitive auxiliary rule. -/
def finiteMark {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (n : Nat) : AuxTerm Symbol arity Gamma tau → Option (AuxTerm Symbol arity Gamma tau)
  | .var _ => none
  | .lam body => (finiteMark n body).map .lam
  | .app _ _ => none
  | .bottom _ => none
  | .ordinary f base => some (.numbered n f (headResult f) base [] .nil)
  | .numbered _ _ _ _ _ _ => none

def selfArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
    (types : List Ty) → AuxArguments Symbol arity Gamma types
  | [] => .nil
  | tau::types => .cons (.numbered n f tau base extraTypes extras)
      (selfArguments n f base extraTypes extras types)

def applyArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types) :
    AuxTerm Symbol arity Gamma tau :=
  match types,args with
  | [],.nil => q
  | _::_,.cons a rest => applyArguments (.app q a) rest

def openNumbered {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (f : Head Symbol) (sigma tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
    AuxTerm Symbol arity (sigma::Gamma) tau :=
  .numbered n f tau (NumberedRewriteSyntax.renameArguments base (Renaming.weaken Gamma sigma))
    (extraTypes++[sigma])
    (NumberedRewriteSyntax.appendArguments
      (NumberedRewriteSyntax.renameArguments extras (Renaming.weaken Gamma sigma)) (.cons (.var .here) .nil))

inductive PrimitiveMark (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :
    Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | mk {tau} (n : Nat) (q r : AuxTerm Symbol arity Gamma tau) : finiteMark n q=some r →
      PrimitiveMark Symbol arity Gamma ⟨tau,q⟩ ⟨tau,r⟩

/-- The literal strict multiset extension of primitive omega-to-finite marks:
retained occurrences are equal, removed is nonempty, and each inserted
occurrence is marked from an actual removed occurrence. -/
def PrimitiveMultiset {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ss ts : List (Packed Symbol arity Gamma)) : Prop :=
  ∃ kept removed inserted,ss.Perm (kept++removed) ∧ ts.Perm (kept++inserted) ∧ removed≠[] ∧
    ∀ q∈inserted,∃ s∈removed,PrimitiveMark Symbol arity Gamma s q

mutual
inductive RawStep (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    (Gamma : List Ty) → (tau : Ty) → AuxTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | put {Gamma} (n : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      RawStep Symbol arity above Gamma (headResult f) (.ordinary f base) (.numbered n f (headResult f) base [] .nil)
  | select {Gamma tau} (n : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty)
      (selected : AuxTerm Symbol arity Gamma (arrows types tau)) :
      (⟨arrows types tau,selected⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras →
      RawStep Symbol arity above Gamma tau (.numbered (n+1) f tau base extraTypes extras)
        (applyArguments selected (selfArguments n f base extraTypes extras types))
  | copy {Gamma} (n : Nat) (f g : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      RecursiveComparison.headAbove above f g →
      RawStep Symbol arity above Gamma (headResult g) (.numbered (n+1) f (headResult g) base extraTypes extras)
        (.ordinary g (selfArguments n f base extraTypes extras (headArguments arity g)))
  | mul {Gamma} (n : Nat) (f g : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes)
      (target : AuxArguments Symbol arity Gamma (headArguments arity g)) :
      RecursiveComparison.headEquivalent f g → PrimitiveMultiset (argumentList base) (argumentList target) →
      RawStep Symbol arity above Gamma (headResult g) (.numbered (n+1) f (headResult g) base extraTypes extras) (.ordinary g target)
  | abs {Gamma sigma tau} (n : Nat) (f : Head Symbol)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      RawStep Symbol arity above Gamma (.arrow sigma tau) (.numbered (n+1) f (.arrow sigma tau) base extraTypes extras)
        (.lam (openNumbered n f sigma tau base extraTypes extras))
  | ordinaryArguments {Gamma} (f : Head Symbol)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      ArgumentStep Symbol arity above Gamma (headArguments arity f) base target →
      RawStep Symbol arity above Gamma (headResult f) (.ordinary f base) (.ordinary f target)
  | numberedBase {Gamma} (n : Nat) (f : Head Symbol) (tau : Ty)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      ArgumentStep Symbol arity above Gamma (headArguments arity f) base target →
      RawStep Symbol arity above Gamma tau (.numbered n f tau base extraTypes extras) (.numbered n f tau target extraTypes extras)
  | numberedExtras {Gamma} (n : Nat) (f : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras target : AuxArguments Symbol arity Gamma extraTypes) :
      ArgumentStep Symbol arity above Gamma extraTypes extras target →
      RawStep Symbol arity above Gamma tau (.numbered n f tau base extraTypes extras) (.numbered n f tau base extraTypes target)
  | appFunction {Gamma sigma tau} (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (a : AuxTerm Symbol arity Gamma sigma) :
      RawStep Symbol arity above Gamma (.arrow sigma tau) q r →
      RawStep Symbol arity above Gamma tau (.app q a) (.app r a)
  | lam {Gamma sigma tau} (q r : AuxTerm Symbol arity (sigma::Gamma) tau) :
      RawStep Symbol arity above (sigma::Gamma) tau q r →
      RawStep Symbol arity above Gamma (.arrow sigma tau) (.lam q) (.lam r)
  | beta {Gamma sigma tau} (body : AuxTerm Symbol arity (sigma::Gamma) tau) (a : AuxTerm Symbol arity Gamma sigma) :
      RawStep Symbol arity above Gamma tau (.app (.lam body) a)
        (NumberedRewriteSyntax.substitute body (singleSubstitution a))
  | bottom {Gamma tau} (q : AuxTerm Symbol arity Gamma tau) : q≠.bottom tau →
      RawStep Symbol arity above Gamma tau q (.bottom tau)
inductive ArgumentStep (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    (Gamma : List Ty) → (types : List Ty) → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | head {Gamma sigma types} (q r : AuxTerm Symbol arity Gamma sigma) (rest : AuxArguments Symbol arity Gamma types) :
      RawStep Symbol arity above Gamma sigma q r → ArgumentStep Symbol arity above Gamma (sigma::types) (.cons q rest) (.cons r rest)
  | tail {Gamma sigma types} (q : AuxTerm Symbol arity Gamma sigma) (rest target : AuxArguments Symbol arity Gamma types) :
      ArgumentStep Symbol arity above Gamma types rest target →
      ArgumentStep Symbol arity above Gamma (sigma::types) (.cons q rest) (.cons q target)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteReduction
