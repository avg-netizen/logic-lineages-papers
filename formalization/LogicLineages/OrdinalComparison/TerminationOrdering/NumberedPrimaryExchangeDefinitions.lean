module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchange
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence

mutual
inductive Exchange (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) :
    (Gamma : List Ty) → Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | ordinary {Gamma} (f g : Head Symbol)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (target : AuxArguments Symbol arity Gamma (headArguments arity g)) :
      HeadInWindow arity symbols S f → HeadInWindow arity symbols S g →
      RecursiveComparison.headEquivalent f g → headResult f=headResult g →
      (argumentList base).Perm (argumentList target) →
      Exchange Symbol arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ ⟨headResult g,.ordinary g target⟩
  | numbered {Gamma} (k : Nat) (f g : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (target : AuxArguments Symbol arity Gamma (headArguments arity g))
      (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) :
      HeadInWindow arity symbols S f → HeadInWindow arity symbols S g →
      RecursiveComparison.headEquivalent f g → (argumentList base).Perm (argumentList target) →
      Exchange Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k g tau target types extras⟩
  | lam {Gamma sigma tau} (q r : AuxTerm Symbol arity (sigma::Gamma) tau) :
      Exchange Symbol arity symbols S (sigma::Gamma) ⟨tau,q⟩ ⟨tau,r⟩ →
      Exchange Symbol arity symbols S Gamma ⟨.arrow sigma tau,.lam q⟩ ⟨.arrow sigma tau,.lam r⟩
  | appFunction {Gamma sigma tau} (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a : AuxTerm Symbol arity Gamma sigma) :
      Exchange Symbol arity symbols S Gamma ⟨.arrow sigma tau,q⟩ ⟨.arrow sigma tau,r⟩ →
      Exchange Symbol arity symbols S Gamma ⟨tau,.app q a⟩ ⟨tau,.app r a⟩
  | appArgument {Gamma sigma tau} (q : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a b : AuxTerm Symbol arity Gamma sigma) :
      Exchange Symbol arity symbols S Gamma ⟨sigma,a⟩ ⟨sigma,b⟩ →
      Exchange Symbol arity symbols S Gamma ⟨tau,.app q a⟩ ⟨tau,.app q b⟩
  | ordinaryArguments {Gamma} (f : Head Symbol)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      ArgumentExchange Symbol arity symbols S Gamma (headArguments arity f) base target →
      Exchange Symbol arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ ⟨headResult f,.ordinary f target⟩
  | numberedBase {Gamma} (k : Nat) (f : Head Symbol) (tau : Ty)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) :
      ArgumentExchange Symbol arity symbols S Gamma (headArguments arity f) base target →
      Exchange Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k f tau target types extras⟩
  | numberedExtras {Gamma} (k : Nat) (f : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (types : List Ty) (extras target : AuxArguments Symbol arity Gamma types) :
      ArgumentExchange Symbol arity symbols S Gamma types extras target →
      Exchange Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k f tau base types target⟩
inductive ArgumentExchange (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) :
    (Gamma types : List Ty) → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | head {Gamma sigma types} (q r : AuxTerm Symbol arity Gamma sigma)
      (rest : AuxArguments Symbol arity Gamma types) :
      Exchange Symbol arity symbols S Gamma ⟨sigma,q⟩ ⟨sigma,r⟩ →
      ArgumentExchange Symbol arity symbols S Gamma (sigma::types) (.cons q rest) (.cons r rest)
  | tail {Gamma sigma types} (q : AuxTerm Symbol arity Gamma sigma)
      (rest target : AuxArguments Symbol arity Gamma types) :
      ArgumentExchange Symbol arity symbols S Gamma types rest target →
      ArgumentExchange Symbol arity symbols S Gamma (sigma::types) (.cons q rest) (.cons q target)
end

inductive Chain {alpha : Type} (R : alpha → alpha → Prop) : alpha → alpha → Prop where
  | refl (a : alpha) : Chain R a a
  | step {a b : alpha} : R a b → Chain R a b
  | trans {a b c : alpha} : Chain R a b → Chain R b c → Chain R a c

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchange
