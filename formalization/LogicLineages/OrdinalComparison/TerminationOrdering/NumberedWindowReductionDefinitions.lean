module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsProof

@[expose] public section
/-! Source06 fixed-window auxiliary primitive instances. This copies the actual
RawStep constructors and adds only a finite head-window guard at Copy and Mul.
No target-confinement or recursive success condition is a constructor premise.
Erasure and universe preservation are separate targets; coverage of simulated
paths and restricted primary equivalence are not claimed here. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReduction
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse

mutual
inductive WindowStep (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) :
    (Gamma : List Ty) → (tau : Ty) → AuxTerm Symbol arity Gamma tau → AuxTerm Symbol arity Gamma tau → Prop where
  | put {Gamma} (n : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      WindowStep Symbol arity symbols S above Gamma (headResult f) (.ordinary f base) (.numbered n f (headResult f) base [] .nil)
  | select {Gamma tau} (n : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty)
      (selected : AuxTerm Symbol arity Gamma (arrows types tau)) :
      (⟨arrows types tau,selected⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras →
      WindowStep Symbol arity symbols S above Gamma tau (.numbered (n+1) f tau base extraTypes extras)
        (applyArguments selected (selfArguments n f base extraTypes extras types))
  | copy {Gamma} (n : Nat) (f g : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      RecursiveComparison.headAbove above f g → HeadInWindow arity symbols S g →
      WindowStep Symbol arity symbols S above Gamma (headResult g) (.numbered (n+1) f (headResult g) base extraTypes extras)
        (.ordinary g (selfArguments n f base extraTypes extras (headArguments arity g)))
  | mul {Gamma} (n : Nat) (f g : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes)
      (target : AuxArguments Symbol arity Gamma (headArguments arity g)) :
      RecursiveComparison.headEquivalent f g → PrimitiveMultiset (argumentList base) (argumentList target) →
      HeadInWindow arity symbols S g →
      WindowStep Symbol arity symbols S above Gamma (headResult g) (.numbered (n+1) f (headResult g) base extraTypes extras) (.ordinary g target)
  | abs {Gamma sigma tau} (n : Nat) (f : Head Symbol)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) (.numbered (n+1) f (.arrow sigma tau) base extraTypes extras)
        (.lam (openNumbered n f sigma tau base extraTypes extras))
  | ordinaryArguments {Gamma} (f : Head Symbol)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      WindowArgumentStep Symbol arity symbols S above Gamma (headArguments arity f) base target →
      WindowStep Symbol arity symbols S above Gamma (headResult f) (.ordinary f base) (.ordinary f target)
  | numberedBase {Gamma} (n : Nat) (f : Head Symbol) (tau : Ty)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) :
      WindowArgumentStep Symbol arity symbols S above Gamma (headArguments arity f) base target →
      WindowStep Symbol arity symbols S above Gamma tau (.numbered n f tau base extraTypes extras) (.numbered n f tau target extraTypes extras)
  | numberedExtras {Gamma} (n : Nat) (f : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras target : AuxArguments Symbol arity Gamma extraTypes) :
      WindowArgumentStep Symbol arity symbols S above Gamma extraTypes extras target →
      WindowStep Symbol arity symbols S above Gamma tau (.numbered n f tau base extraTypes extras) (.numbered n f tau base extraTypes target)
  | appFunction {Gamma sigma tau} (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (a : AuxTerm Symbol arity Gamma sigma) :
      WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) q r →
      WindowStep Symbol arity symbols S above Gamma tau (.app q a) (.app r a)
  | lam {Gamma sigma tau} (q r : AuxTerm Symbol arity (sigma::Gamma) tau) :
      WindowStep Symbol arity symbols S above (sigma::Gamma) tau q r →
      WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) (.lam q) (.lam r)
  | beta {Gamma sigma tau} (body : AuxTerm Symbol arity (sigma::Gamma) tau) (a : AuxTerm Symbol arity Gamma sigma) :
      WindowStep Symbol arity symbols S above Gamma tau (.app (.lam body) a)
        (NumberedRewriteSyntax.substitute body (singleSubstitution a))
  | bottom {Gamma tau} (q : AuxTerm Symbol arity Gamma tau) : q≠.bottom tau →
      WindowStep Symbol arity symbols S above Gamma tau q (.bottom tau)
inductive WindowArgumentStep (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) :
    (Gamma : List Ty) → (types : List Ty) → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | head {Gamma sigma types} (q r : AuxTerm Symbol arity Gamma sigma) (rest : AuxArguments Symbol arity Gamma types) :
      WindowStep Symbol arity symbols S above Gamma sigma q r → WindowArgumentStep Symbol arity symbols S above Gamma (sigma::types) (.cons q rest) (.cons r rest)
  | tail {Gamma sigma types} (q : AuxTerm Symbol arity Gamma sigma) (rest target : AuxArguments Symbol arity Gamma types) :
      WindowArgumentStep Symbol arity symbols S above Gamma types rest target →
      WindowArgumentStep Symbol arity symbols S above Gamma (sigma::types) (.cons q rest) (.cons q target)
end


end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReduction
