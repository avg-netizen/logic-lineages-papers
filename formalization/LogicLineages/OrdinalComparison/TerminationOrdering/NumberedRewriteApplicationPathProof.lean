module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationPathProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

theorem trans {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {tau : Ty} {q r s : AuxTerm Symbol arity Gamma tau}
    (first : RawSteps Symbol arity above Gamma tau q r) (last : RawSteps Symbol arity above Gamma tau r s) :
    RawSteps Symbol arity above Gamma tau q s := by
  induction first with
  | refl => exact last
  | next q r s h rest ih => exact .next _ _ _ h (ih last)

theorem appFunction {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {sigma tau : Ty} {q r : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    (h : RawSteps Symbol arity above Gamma (.arrow sigma tau) q r) (a : AuxTerm Symbol arity Gamma sigma) :
    RawSteps Symbol arity above Gamma tau (.app q a) (.app r a) := by
  induction h with
  | refl => exact .refl _
  | next q r s h rest ih => exact .next _ _ _ (.appFunction q r a h) ih

theorem applyArgumentsPath {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma types : List Ty} {tau : Ty} (q r : AuxTerm Symbol arity Gamma (arrows types tau))
    (args : AuxArguments Symbol arity Gamma types)
    (h : RawSteps Symbol arity above Gamma (arrows types tau) q r) :
    RawSteps Symbol arity above Gamma tau
      (NumberedRewriteReduction.applyArguments q args) (NumberedRewriteReduction.applyArguments r args) := by
  induction types with
  | nil => cases args; exact h
  | cons sigma types ih => cases args with
    | cons a rest => exact ih (.app q a) (.app r a) rest (appFunction h a)

theorem tupleRightUnit {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (a : ExtraTuple Symbol arity Gamma) : appendTuple a ⟨[],.nil⟩=a := by
  rcases a with ⟨types,values⟩
  induction types with
  | nil => cases values; rfl
  | cons sigma types ih => cases values with
    | cons q rest => exact congrArg (prependTuple q) (ih rest)

theorem tupleAssoc {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (a b c : ExtraTuple Symbol arity Gamma) : appendTuple (appendTuple a b) c=appendTuple a (appendTuple b c) := by
  rcases a with ⟨types,values⟩
  induction types with
  | nil => cases values; rfl
  | cons sigma types ih => cases values with
    | cons q rest => exact congrArg (prependTuple q) (ih rest)

theorem oneArgument {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (n : Nat) (Gamma : List Ty) (sigma tau : Ty) (f : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (a : AuxTerm Symbol arity Gamma sigma) :
    RawSteps Symbol arity above Gamma tau (.app (.numbered (n+1) f (.arrow sigma tau) base extraTypes extras) a)
      (.numbered n f tau base (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil))) := by
  exact .next _ _ _ (.appFunction _ _ a (.abs n f base extraTypes extras))
    (.next _ _ _ (NumberedRewriteApplicationBindingProof.openNumberedBeta Symbol arity above n Gamma sigma tau f base extraTypes extras a) (.refl _))

theorem numberedWholeTuple : NumberedRewriteApplicationTargets.ActualNumberedWholeTuple := by
  intro Symbol arity above n Gamma tau f base extraTypes extras types args
  induction types generalizing extraTypes with
  | nil =>
    cases args
    simp only [List.length_nil,Nat.add_zero,NumberedRewriteReduction.applyArguments]
    have ht := congrArg (numberedFromTuple n f tau base) (tupleRightUnit (⟨extraTypes,extras⟩ : ExtraTuple Symbol arity Gamma))
    change AuxTerm.numbered n f tau base (extraTypes++[]) (NumberedRewriteSyntax.appendArguments extras .nil)=
      AuxTerm.numbered n f tau base extraTypes extras at ht
    rw [ht]
    exact .refl _
  | cons sigma types ih =>
    cases args with
    | cons a rest =>
      have hone := oneArgument above (n+types.length) Gamma sigma (arrows types tau) f base extraTypes extras a
      have hlift := applyArgumentsPath _ _ rest hone
      have htail := ih (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)) rest
      have hpath := trans hlift htail
      have ht := congrArg (numberedFromTuple n f tau base)
        (tupleAssoc (⟨extraTypes,extras⟩ : ExtraTuple Symbol arity Gamma) ⟨[sigma],.cons a .nil⟩ ⟨types,rest⟩)
      change AuxTerm.numbered n f tau base ((extraTypes++[sigma])++types)
          (NumberedRewriteSyntax.appendArguments (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)) rest)=
        AuxTerm.numbered n f tau base (extraTypes++(sigma::types))
          (NumberedRewriteSyntax.appendArguments extras (.cons a rest)) at ht
      rw [ht] at hpath
      simpa only [List.length_cons,Nat.add_assoc,NumberedRewriteReduction.applyArguments,arrows] using hpath

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationPathProof
