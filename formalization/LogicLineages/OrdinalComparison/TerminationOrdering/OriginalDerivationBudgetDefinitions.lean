module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTransitivityTargets

@[expose] public section
/-! Finite inference-height presentation of the IMMUTABLE ORIGINAL rules.
Up only pads the proof budget and must erase to the identical original proof.
No relation-transitivity rule or new semantic comparison is introduced. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudget
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison

mutual
inductive Weak (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    Nat → (Gamma : List Ty) → Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | var {Gamma sigma} (n : Nat) (v : Variable Gamma sigma) : Weak Symbol arity above (n+1) Gamma ⟨sigma,.var v⟩ ⟨sigma,.var v⟩
  | abs {Gamma sigma tau} (n : Nat) (s t : MarkedTerm Symbol arity (sigma::Gamma) tau) :
      Weak Symbol arity above n (sigma::Gamma) ⟨tau,s⟩ ⟨tau,t⟩ →
      Weak Symbol arity above (n+1) Gamma ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩
  | fun_ {Gamma} (n : Nat) (f g : Head Symbol)
      (ss : Arguments Symbol arity Gamma (headArguments arity f)) (ts : Arguments Symbol arity Gamma (headArguments arity g))
      (matched : List (Packed Symbol arity Gamma)) :
      headEquivalent f g → headResult f=headResult g → (argumentList ts).Perm matched →
      WeakMatch Symbol arity above n Gamma (argumentList ss) matched →
      Weak Symbol arity above (n+1) Gamma ⟨_,.ordinary f ss⟩ ⟨_,.ordinary g ts⟩
  | put {Gamma} (n : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (t : MarkedTerm Symbol arity Gamma (headResult f)) :
      Weak Symbol arity above n Gamma ⟨_,.marked f (headResult f) base [] .nil⟩ ⟨_,t⟩ →
      Weak Symbol arity above (n+1) Gamma ⟨_,.ordinary f base⟩ ⟨_,t⟩
  | select {Gamma sigma tau} (n : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (types : List Ty)
      (q : MarkedTerm Symbol arity Gamma sigma) (r t : MarkedTerm Symbol arity Gamma tau) (suffix : sigma=arrows types tau) :
      (⟨sigma,q⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras →
      applyOriginalWith q (fun v => .var v) (selfArguments f base extraTypes extras types) suffix=some r →
      Weak Symbol arity above n Gamma ⟨tau,r⟩ ⟨tau,t⟩ →
      Weak Symbol arity above (n+1) Gamma ⟨tau,.marked f tau base extraTypes extras⟩ ⟨tau,t⟩
  | fAbs {Gamma sigma tau} (n : Nat) (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (t : MarkedTerm Symbol arity (sigma::Gamma) tau) :
      Weak Symbol arity above n (sigma::Gamma) ⟨tau,openMarked f sigma tau base extraTypes extras⟩ ⟨tau,t⟩ →
      Weak Symbol arity above (n+1) Gamma ⟨.arrow sigma tau,.marked f (.arrow sigma tau) base extraTypes extras⟩ ⟨.arrow sigma tau,.lam t⟩
  | copy {Gamma} (n : Nat) (f g : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes)
      (target : Arguments Symbol arity Gamma (headArguments arity g)) :
      headAbove above f g →
      (∀ p∈argumentList target,Weak Symbol arity above n Gamma ⟨p.1,.marked f p.1 base extraTypes extras⟩ p) →
      Weak Symbol arity above (n+1) Gamma ⟨_,.marked f (headResult g) base extraTypes extras⟩ ⟨_,.ordinary g target⟩
  | stat {Gamma} (n : Nat) (f g : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes)
      (target : Arguments Symbol arity Gamma (headArguments arity g)) :
      headEquivalent f g → StrictMultiset Symbol arity above n Gamma (argumentList base) (argumentList target) →
      (∀ p∈argumentList target,Weak Symbol arity above n Gamma ⟨p.1,.marked f p.1 base extraTypes extras⟩ p) →
      Weak Symbol arity above (n+1) Gamma ⟨_,.marked f (headResult g) base extraTypes extras⟩ ⟨_,.ordinary g target⟩
  | up {Gamma} (n : Nat) (s t : Packed Symbol arity Gamma) : Weak Symbol arity above n Gamma s t → Weak Symbol arity above (n+1) Gamma s t
inductive Strict (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    Nat → (Gamma : List Ty) → Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | mark {Gamma tau} (n : Nat) (s r t : MarkedTerm Symbol arity Gamma tau) : strictMark s=some r →
      Weak Symbol arity above n Gamma ⟨tau,r⟩ ⟨tau,t⟩ → Strict Symbol arity above (n+1) Gamma ⟨tau,s⟩ ⟨tau,t⟩
  | up {Gamma} (n : Nat) (s t : Packed Symbol arity Gamma) : Strict Symbol arity above n Gamma s t → Strict Symbol arity above (n+1) Gamma s t
inductive WeakMatch (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    Nat → (Gamma : List Ty) → List (Packed Symbol arity Gamma) → List (Packed Symbol arity Gamma) → Prop where
  | nil {Gamma} (n : Nat) : WeakMatch Symbol arity above (n+1) Gamma [] []
  | cons {Gamma} (n : Nat) (s t : Packed Symbol arity Gamma) (ss ts : List (Packed Symbol arity Gamma)) :
      Weak Symbol arity above n Gamma s t → WeakMatch Symbol arity above n Gamma ss ts →
      WeakMatch Symbol arity above (n+1) Gamma (s::ss) (t::ts)
  | up {Gamma} (n : Nat) (ss ts : List (Packed Symbol arity Gamma)) : WeakMatch Symbol arity above n Gamma ss ts → WeakMatch Symbol arity above (n+1) Gamma ss ts
inductive StrictMultiset (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    Nat → (Gamma : List Ty) → List (Packed Symbol arity Gamma) → List (Packed Symbol arity Gamma) → Prop where
  | replace {Gamma} (n : Nat) (ss ts kept retained removed inserted : List (Packed Symbol arity Gamma)) :
      ss.Perm (kept++removed) → ts.Perm (retained++inserted) → removed≠[] →
      WeakMatch Symbol arity above n Gamma kept retained → ReplacementMatch Symbol arity above n Gamma removed inserted →
      StrictMultiset Symbol arity above (n+1) Gamma ss ts
  | up {Gamma} (n : Nat) (ss ts : List (Packed Symbol arity Gamma)) : StrictMultiset Symbol arity above n Gamma ss ts → StrictMultiset Symbol arity above (n+1) Gamma ss ts
inductive ReplacementMatch (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop) :
    Nat → (Gamma : List Ty) → List (Packed Symbol arity Gamma) → List (Packed Symbol arity Gamma) → Prop where
  | nil {Gamma} (n : Nat) (removed : List (Packed Symbol arity Gamma)) : ReplacementMatch Symbol arity above (n+1) Gamma removed []
  | cons {Gamma} (n : Nat) (removed : List (Packed Symbol arity Gamma)) (s t : Packed Symbol arity Gamma)
      (rest : List (Packed Symbol arity Gamma)) :
      s∈removed → Strict Symbol arity above n Gamma s t → ReplacementMatch Symbol arity above n Gamma removed rest →
      ReplacementMatch Symbol arity above (n+1) Gamma removed (t::rest)
  | up {Gamma} (n : Nat) (ss ts : List (Packed Symbol arity Gamma)) : ReplacementMatch Symbol arity above n Gamma ss ts → ReplacementMatch Symbol arity above (n+1) Gamma ss ts
end

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudget
