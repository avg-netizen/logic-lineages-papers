module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionProof

@[expose] public section
/-! Fixed-window primary motion. The only new generator premises constrain
BOTH exchanged heads to the actual finite window, so symmetry cannot import
an unbounded native annotation. All labels, types, base permutations and extra
orders are original. No endpoint confinement premise or finiteness assertion. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalence
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse

mutual
inductive WindowPrimary (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) :
    (Gamma : List Ty) → Packed Symbol arity Gamma → Packed Symbol arity Gamma → Prop where
  | refl {Gamma} (q : Packed Symbol arity Gamma) : WindowPrimary Symbol arity symbols S Gamma q q
  | symm {Gamma} {q r : Packed Symbol arity Gamma} :
      WindowPrimary Symbol arity symbols S Gamma q r → WindowPrimary Symbol arity symbols S Gamma r q
  | trans {Gamma} {q r s : Packed Symbol arity Gamma} :
      WindowPrimary Symbol arity symbols S Gamma q r → WindowPrimary Symbol arity symbols S Gamma r s → WindowPrimary Symbol arity symbols S Gamma q s
  | ordinary {Gamma} (f g : Head Symbol)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (target : AuxArguments Symbol arity Gamma (headArguments arity g)) :
      HeadInWindow arity symbols S f → HeadInWindow arity symbols S g →
      RecursiveComparison.headEquivalent f g → headResult f=headResult g →
      (argumentList base).Perm (argumentList target) →
      WindowPrimary Symbol arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ ⟨headResult g,.ordinary g target⟩
  | numbered {Gamma} (k : Nat) (f g : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (target : AuxArguments Symbol arity Gamma (headArguments arity g))
      (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) :
      HeadInWindow arity symbols S f → HeadInWindow arity symbols S g →
      RecursiveComparison.headEquivalent f g → (argumentList base).Perm (argumentList target) →
      WindowPrimary Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k g tau target types extras⟩
  | lam {Gamma sigma tau} (q r : AuxTerm Symbol arity (sigma::Gamma) tau) :
      WindowPrimary Symbol arity symbols S (sigma::Gamma) ⟨tau,q⟩ ⟨tau,r⟩ →
      WindowPrimary Symbol arity symbols S Gamma ⟨.arrow sigma tau,.lam q⟩ ⟨.arrow sigma tau,.lam r⟩
  | appFunction {Gamma sigma tau} (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a : AuxTerm Symbol arity Gamma sigma) :
      WindowPrimary Symbol arity symbols S Gamma ⟨.arrow sigma tau,q⟩ ⟨.arrow sigma tau,r⟩ →
      WindowPrimary Symbol arity symbols S Gamma ⟨tau,.app q a⟩ ⟨tau,.app r a⟩
  | appArgument {Gamma sigma tau} (q : AuxTerm Symbol arity Gamma (.arrow sigma tau))
      (a b : AuxTerm Symbol arity Gamma sigma) :
      WindowPrimary Symbol arity symbols S Gamma ⟨sigma,a⟩ ⟨sigma,b⟩ →
      WindowPrimary Symbol arity symbols S Gamma ⟨tau,.app q a⟩ ⟨tau,.app q b⟩
  | ordinaryArguments {Gamma} (f : Head Symbol)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f)) :
      WindowArgumentPrimary Symbol arity symbols S Gamma (headArguments arity f) base target →
      WindowPrimary Symbol arity symbols S Gamma ⟨headResult f,.ordinary f base⟩ ⟨headResult f,.ordinary f target⟩
  | numberedBase {Gamma} (k : Nat) (f : Head Symbol) (tau : Ty)
      (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments Symbol arity Gamma types) :
      WindowArgumentPrimary Symbol arity symbols S Gamma (headArguments arity f) base target →
      WindowPrimary Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k f tau target types extras⟩
  | numberedExtras {Gamma} (k : Nat) (f : Head Symbol) (tau : Ty)
      (base : AuxArguments Symbol arity Gamma (headArguments arity f))
      (types : List Ty) (extras target : AuxArguments Symbol arity Gamma types) :
      WindowArgumentPrimary Symbol arity symbols S Gamma types extras target →
      WindowPrimary Symbol arity symbols S Gamma ⟨tau,.numbered k f tau base types extras⟩ ⟨tau,.numbered k f tau base types target⟩
inductive WindowArgumentPrimary (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) :
    (Gamma types : List Ty) → AuxArguments Symbol arity Gamma types → AuxArguments Symbol arity Gamma types → Prop where
  | nil {Gamma} : WindowArgumentPrimary Symbol arity symbols S Gamma [] .nil .nil
  | cons {Gamma sigma types} (q r : AuxTerm Symbol arity Gamma sigma)
      (rest target : AuxArguments Symbol arity Gamma types) :
      WindowPrimary Symbol arity symbols S Gamma ⟨sigma,q⟩ ⟨sigma,r⟩ → WindowArgumentPrimary Symbol arity symbols S Gamma types rest target →
      WindowArgumentPrimary Symbol arity symbols S Gamma (sigma::types) (.cons q rest) (.cons r target)
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalence
