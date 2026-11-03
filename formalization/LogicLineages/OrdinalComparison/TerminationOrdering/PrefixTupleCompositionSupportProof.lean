module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening PrefixSourceComposition

theorem packedAppendAssociativity {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys zs : List Ty}
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) (c : Arguments Symbol arity Gamma zs) :
    (⟨(xs++ys)++zs,appendArguments (appendArguments a b) c⟩ : Sigma (Arguments Symbol arity Gamma))=
      ⟨xs++(ys++zs),appendArguments a (appendArguments b c)⟩ := by
  induction xs with
  | nil => cases a; rfl
  | cons sigma xs ih =>
    cases a with
    | cons q rest =>
      exact congrArg (fun args : Sigma (Arguments Symbol arity Gamma) =>
        (⟨sigma::args.1,Arguments.cons q args.2⟩ : Sigma (Arguments Symbol arity Gamma))) (ih rest)

theorem markedAppendAssociativity {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys zs : List Ty}
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) (c : Arguments Symbol arity Gamma zs) :
    MarkedTerm.marked f tau base ((xs++ys)++zs) (appendArguments (appendArguments a b) c)=
      MarkedTerm.marked f tau base (xs++(ys++zs)) (appendArguments a (appendArguments b c)) :=
  congrArg (fun args : Sigma (Arguments Symbol arity Gamma) => MarkedTerm.marked f tau base args.1 args.2)
    (packedAppendAssociativity a b c)

theorem emptyFirst {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta extraTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Delta (headArguments arity f))
    (extras : Arguments Symbol arity Delta extraTypes) (sigma tau : Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (args : Arguments Symbol arity Delta types)
    (H : ∀ rho (v : Variable Gamma rho),PrefixImage f base extras (env v))
    (hc : SourceExtendedComparison.PrefixCopies f base extras args)
    (suffix : sigma=arrows types tau) (intermediate : MarkedTerm Symbol arity Delta sigma)
    (r : MarkedTerm Symbol arity Delta tau)
    (hfirst : applyOriginalWith q env .nil rfl=some intermediate)
    (hsecond : applyOriginalWith intermediate (fun v => .var v) args suffix=some r) :
    applyOriginalWith q env args suffix=some r ∨ Sharp Symbol arity Delta (.marked f tau base extraTypes extras) r := by
  have hi : substituteTerm q env=intermediate := Option.some.inj ((SuccessfulApplicationPostProof.emptyWith q env).symm.trans hfirst)
  subst intermediate
  have H' : ∀ rho (v : Variable Gamma rho),PrefixImage f base extras (substituteTerm (env v) (fun v => .var v)) := by
    intro rho v
    rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1]
    exact H _ v
  have hout := PrefixSourceCompositionProof.guardedSourceComposition Symbol arity Gamma Delta Delta f base extraTypes extras
    sigma tau types q env (fun v => .var v) args H' hc suffix r hsecond
  have he : (fun {rho} (v : Variable Gamma rho) => substituteTerm (env v) (fun v => .var v))=(@env) := by
    funext rho v
    exact SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Delta rho (env v)
  rw [he] at hout
  exact hout

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionSupportProof
