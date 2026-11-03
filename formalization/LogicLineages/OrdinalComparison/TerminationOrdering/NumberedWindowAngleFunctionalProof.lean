module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleFunctionalProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication NumberedOriginalAngle
open NumberedOriginalAngleSupportProof NumberedWindowTraces

theorem ordinaryCase {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (n : Nat)
    {Gamma Delta : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (env : MarkedSubstitution Symbol arity Gamma Delta) (types : List Ty) (tau : Ty)
    (args : Arguments Symbol arity Delta types) (hn : types≠[]) (suffix : headResult f=arrows types tau)
    (r : MarkedTerm Symbol arity Delta tau)
    (h : applyOriginalWith (.ordinary f base) env args suffix=some r)
    (Q : AuxTerm Symbol arity Delta (headResult f)) (values : AuxArguments Symbol arity Delta types)
    (hQ : Represents Symbol arity (n+types.length) Delta (headResult f)
      (substituteTerm (.ordinary f base) env) Q)
    (hvalues : ArgumentsRepresent Symbol arity (n+types.length) Delta types args values) :
    ∃ R m,WindowTypedTrace Symbol arity symbols S above Delta tau m (NumberedRewriteReduction.applyArguments (transportAux suffix Q) values) R ∧
      Represents Symbol arity n Delta tau r R := by
  cases types with
  | nil => exact (hn rfl).elim
  | cons sigma types =>
    cases args with
    | cons a rest =>
      obtain ⟨B,hpacked,hB⟩ := NumberedPositiveMarkProof.ordinaryRepresentation
        (substituteTerm (.ordinary f base) env) Q hQ f (Source.SourceMarkedBinding.substituteArguments base env) rfl
      have hQeq : Q=AuxTerm.ordinary f B := by injection hpacked
      subst Q
      have hr : MarkedTerm.marked f tau (Source.SourceMarkedBinding.substituteArguments base env)
          (sigma::types) (.cons a rest)=r := Option.some.inj h
      subst r
      have hput : WindowTypedTrace Symbol arity symbols S above Delta (headResult f) 1 (.ordinary f B)
          (.numbered (n+(sigma::types).length) f (headResult f) B [] .nil) :=
        .raw (.put _ f B)
      have hc := NumberedWindowAngleSupportProof.transportPaths suffix hput
      rw [transportNumbered] at hc
      have hp := WindowTypedTrace.trans
        (NumberedWindowApplicationProof.completeFunctionContext Symbol arity symbols S above Delta _ tau 1 _ _ values hc)
        (NumberedWindowApplicationProof.numberedWholeTuple Symbol arity symbols S above n Delta tau f B [] .nil (sigma::types) values)
      refine ⟨.numbered n f tau B (sigma::types) values,_,hp,?_⟩
      exact .numbered f tau _ B (sigma::types) _ values n (Nat.le_refl _)
        (NumberedPositiveMarkProof.lowerArguments (by omega) _ _ hB)
        (NumberedPositiveMarkProof.lowerArguments (by omega) _ _ hvalues)

theorem markedCase {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (n : Nat)
    {Gamma Delta : List Ty} (sigma : Ty) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes)
    (env : MarkedSubstitution Symbol arity Gamma Delta) (types : List Ty) (tau : Ty)
    (args : Arguments Symbol arity Delta types) (hn : types≠[]) (suffix : sigma=arrows types tau)
    (r : MarkedTerm Symbol arity Delta tau)
    (h : applyOriginalWith (.marked f sigma base extraTypes extras) env args suffix=some r)
    (Q : AuxTerm Symbol arity Delta sigma) (values : AuxArguments Symbol arity Delta types)
    (hQ : Represents Symbol arity (n+types.length) Delta sigma
      (substituteTerm (.marked f sigma base extraTypes extras) env) Q)
    (hvalues : ArgumentsRepresent Symbol arity (n+types.length) Delta types args values) :
    ∃ R m,WindowTypedTrace Symbol arity symbols S above Delta tau m (NumberedRewriteReduction.applyArguments (transportAux suffix Q) values) R ∧
      Represents Symbol arity n Delta tau r R := by
  cases types with
  | nil => exact (hn rfl).elim
  | cons upsilon types =>
    cases args with
    | cons a rest =>
      obtain ⟨k,B,E,hk,hQeq,hB,hE⟩ := numberedRepresentation f
        (Source.SourceMarkedBinding.substituteArguments base env) extraTypes
        (Source.SourceMarkedBinding.substituteArguments extras env) Q hQ
      subst Q
      have hr : MarkedTerm.marked f tau (Source.SourceMarkedBinding.substituteArguments base env)
          (extraTypes++(upsilon::types))
          (Source.SourceMarkedBinding.appendArguments (Source.SourceMarkedBinding.substituteArguments extras env) (.cons a rest))=r := Option.some.inj h
      subst r
      have hlength : (upsilon::types).length≤k := by omega
      have hbudget : n≤k-(upsilon::types).length := by omega
      have hp := NumberedWindowApplicationProof.numberedWholeTuple Symbol arity symbols S above
        (k-(upsilon::types).length) Delta tau f B extraTypes E (upsilon::types) values
      rw [Nat.sub_add_cancel hlength] at hp
      refine ⟨.numbered (k-(upsilon::types).length) f tau B (extraTypes++(upsilon::types))
        (NumberedRewriteSyntax.appendArguments E values),2*(upsilon::types).length,?_,?_⟩
      · simpa only [transportNumbered] using hp
      · exact .numbered f tau _ B _ _ _ _ hbudget
          (NumberedPositiveMarkProof.lowerArguments (by omega) _ _ hB)
          (appendRepresentation _ _ _ _
            (NumberedPositiveMarkProof.lowerArguments (by omega) _ _ hE)
            (NumberedPositiveMarkProof.lowerArguments (by omega) _ _ hvalues))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleFunctionalProof
