module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedPrimaryExchange

def LambdaCases {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (q r : Packed Symbol arity Gamma) : Prop :=
  match q with
  | ⟨_,.lam (sigma := sigma) (tau := tau) body⟩ =>
      ∃ target : AuxTerm Symbol arity (sigma :: Gamma) tau,
        Exchange Symbol arity symbols S (sigma :: Gamma) ⟨tau,body⟩ ⟨tau,target⟩ ∧
        r = ⟨.arrow sigma tau,.lam target⟩
  | _ => True

theorem lambdaCases {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : Exchange Symbol arity symbols S Gamma q r) :
    LambdaCases symbols S q r := by
  induction h using Exchange.rec (motive_2 := fun _ _ _ _ _ => True)
  case lam q r h ih => exact ⟨r,h,rfl⟩
  all_goals trivial

def OrdinaryCases {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (q r : Packed Symbol arity Gamma) : Prop :=
  match q with
  | ⟨_,.ordinary f base⟩ =>
      (∃ (g : Head Symbol) (target : AuxArguments Symbol arity Gamma (headArguments arity g)),
        HeadInWindow arity symbols S f ∧ HeadInWindow arity symbols S g ∧
        RecursiveComparison.headEquivalent f g ∧ headResult f = headResult g ∧
        (argumentList base).Perm (argumentList target) ∧ r = ⟨headResult g,.ordinary g target⟩) ∨
      (∃ target : AuxArguments Symbol arity Gamma (headArguments arity f),
        ArgumentExchange Symbol arity symbols S Gamma (headArguments arity f) base target ∧
        r = ⟨headResult f,.ordinary f target⟩)
  | _ => True

theorem ordinaryCases {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : Exchange Symbol arity symbols S Gamma q r) :
    OrdinaryCases symbols S q r := by
  induction h using Exchange.rec (motive_2 := fun _ _ _ _ _ => True)
  case ordinary f g base target hf hg he ht hp => exact Or.inl ⟨g,target,hf,hg,he,ht,hp,rfl⟩
  case ordinaryArguments f base target h ih => exact Or.inr ⟨target,h,rfl⟩
  all_goals trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeCasesProof
