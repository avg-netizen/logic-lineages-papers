module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalAngle NumberedWindowTraces

theorem transportPaths {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty} {m : Nat}
    (h : sigma=tau) {Q R : AuxTerm Symbol arity Gamma sigma}
    (hp : WindowTypedTrace Symbol arity symbols S above Gamma sigma m Q R) :
    WindowTypedTrace Symbol arity symbols S above Gamma tau m (transportAux h Q) (transportAux h R) := by
  cases h
  exact hp

theorem emptyAngle {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (n : Nat) {Gamma Delta : List Ty} {sigma tau : Ty}
    (q : MarkedTerm Symbol arity Gamma sigma) (env : MarkedSubstitution Symbol arity Gamma Delta)
    (suffix : sigma=tau) (r : MarkedTerm Symbol arity Delta tau)
    (h : applyOriginalWith q env .nil suffix=some r) (Q : AuxTerm Symbol arity Delta sigma)
    (values : AuxArguments Symbol arity Delta [])
    (hQ : Represents Symbol arity n Delta sigma (substituteTerm q env) Q) :
    ∃ (R : AuxTerm Symbol arity Delta tau) (m : Nat),
      WindowTypedTrace Symbol arity symbols S above Delta tau m (applyArguments (transportAux suffix Q) values) R ∧
      Represents Symbol arity n Delta tau r R := by
  cases values
  have he : transportTerm suffix (substituteTerm q env)=r :=
    Option.some.inj ((NumberedOriginalAngleSupportProof.emptyOriginalWith q env suffix).symm.trans h)
  subst r
  exact ⟨transportAux suffix Q,0,.equivalent (.refl _),NumberedOriginalAngleSupportProof.transportRepresentation suffix _ _ hQ⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleSupportProof
