module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication NumberedWindowReduction NumberedWindowEquivalence NumberedWindowTraces

theorem openNumberedBeta : NumberedWindowApplicationTargets.ActualOpenNumberedBeta := by
  intro Symbol arity symbols S above n Gamma sigma tau f base extraTypes extras a
  have hbody := NumberedRewriteApplicationBindingProof.openedBetaBody n sigma tau f base extraTypes extras a
  rw [←hbody]
  exact .beta _ a

theorem completeFunctionContext : NumberedWindowApplicationTargets.ActualCompleteFunctionContext := by
  intro Symbol arity symbols S above Gamma types tau n q r args h
  induction types with
  | nil => cases args; exact h
  | cons sigma types ih => cases args with
    | cons a rest =>
      exact ih (.app q a) (.app r a) rest
        (NumberedWindowTracesProof.functionContext Symbol arity symbols S above Gamma sigma (arrows types tau) n q r a h)

theorem oneArgument {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) (Gamma : List Ty) (sigma tau : Ty) (f : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (a : AuxTerm Symbol arity Gamma sigma) :
    WindowTypedTrace Symbol arity symbols S above Gamma tau 2
      (.app (.numbered (n+1) f (.arrow sigma tau) base extraTypes extras) a)
      (.numbered n f tau base (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil))) := by
  exact .trans (.raw (.appFunction _ _ a (.abs n f base extraTypes extras)))
    (.raw (openNumberedBeta Symbol arity symbols S above n Gamma sigma tau f base extraTypes extras a))

theorem numberedWholeTuple : NumberedWindowApplicationTargets.ActualNumberedWholeTuple := by
  intro Symbol arity symbols S above n Gamma tau f base extraTypes extras types args
  induction types generalizing extraTypes with
  | nil =>
    cases args
    simp only [List.length_nil,Nat.add_zero,Nat.mul_zero,NumberedRewriteReduction.applyArguments]
    have ht := congrArg (numberedFromTuple n f tau base)
      (NumberedRewriteApplicationPathProof.tupleRightUnit (⟨extraTypes,extras⟩ : ExtraTuple Symbol arity Gamma))
    change AuxTerm.numbered n f tau base (extraTypes++[]) (NumberedRewriteSyntax.appendArguments extras .nil)=
      AuxTerm.numbered n f tau base extraTypes extras at ht
    rw [ht]
    exact .equivalent (.refl _)
  | cons sigma types ih =>
    cases args with
    | cons a rest =>
      have hone := oneArgument symbols S above (n+types.length) Gamma sigma (arrows types tau) f base extraTypes extras a
      have hlift := completeFunctionContext Symbol arity symbols S above Gamma types tau 2 _ _ rest hone
      have htail := ih (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)) rest
      have hpath := WindowTypedTrace.trans hlift htail
      have ht := congrArg (numberedFromTuple n f tau base)
        (NumberedRewriteApplicationPathProof.tupleAssoc
          (⟨extraTypes,extras⟩ : ExtraTuple Symbol arity Gamma) ⟨[sigma],.cons a .nil⟩ ⟨types,rest⟩)
      change AuxTerm.numbered n f tau base ((extraTypes++[sigma])++types)
          (NumberedRewriteSyntax.appendArguments (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)) rest)=
        AuxTerm.numbered n f tau base (extraTypes++(sigma::types))
          (NumberedRewriteSyntax.appendArguments extras (.cons a rest)) at ht
      rw [ht] at hpath
      simpa only [List.length_cons,Nat.add_assoc,NumberedRewriteReduction.applyArguments,arrows,
        Nat.mul_add,Nat.mul_one,Nat.add_comm] using hpath

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowApplicationProof
