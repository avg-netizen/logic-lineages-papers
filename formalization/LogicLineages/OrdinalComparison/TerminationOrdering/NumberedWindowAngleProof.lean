module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleFunctionalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication NumberedOriginalAngle
open NumberedOriginalAngleSupportProof NumberedWindowAngleFunctionalProof NumberedWindowTraces

theorem angle {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (n : Nat)
    {Gamma : List Ty} {sigma : Ty} (q : MarkedTerm Symbol arity Gamma sigma) :
    ∀ (Delta : List Ty) (env : MarkedSubstitution Symbol arity Gamma Delta)
      (types : List Ty) (tau : Ty) (args : Arguments Symbol arity Delta types) (suffix : sigma=arrows types tau)
      (r : MarkedTerm Symbol arity Delta tau),applyOriginalWith q env args suffix=some r →
      ∀ (Q : AuxTerm Symbol arity Delta sigma) (values : AuxArguments Symbol arity Delta types),
      Represents Symbol arity (n+types.length) Delta sigma (substituteTerm q env) Q →
      ArgumentsRepresent Symbol arity (n+types.length) Delta types args values →
      ∃ R m,WindowTypedTrace Symbol arity symbols S above Delta tau m
          (NumberedRewriteReduction.applyArguments (transportAux suffix Q) values) R ∧
        Represents Symbol arity n Delta tau r R := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro Delta env types tau args suffix r h Q values hQ hvalues
    cases types with
    | nil => cases args; exact NumberedWindowAngleSupportProof.emptyAngle symbols S above n (.var v) env suffix r h Q values hQ
    | cons upsilon types => cases args with
      | cons a rest => cases h
  | @lam Gamma dom cod body ih =>
    intro Delta env types tau args suffix r h Q values hQ hvalues
    cases types with
    | nil => cases args; exact NumberedWindowAngleSupportProof.emptyAngle symbols S above n (.lam body) env suffix r h Q values hQ
    | cons upsilon types => cases args with
      | cons a rest =>
        obtain ⟨hdom,hcod⟩ := Ty.arrow.inj suffix
        cases hdom
        cases hcod
        change applyOriginalWith body (extendEnvironment env a) rest rfl=some r at h
        obtain ⟨B,hpacked,hB⟩ := NumberedPositiveMarkProof.lambdaRepresentation
          (substituteTerm (.lam body) env) Q hQ _ _
          (substituteTerm body (Source.SourceMarkedBinding.liftSubstitution env)) rfl
        have hQeq : Q=AuxTerm.lam B := by injection hpacked
        subst Q
        obtain ⟨A,V,rfl,hA,hV⟩ := consRepresentation a rest values hvalues
        have hsingle : ∀ (upsilon : Ty) (v : Variable (_::Delta) upsilon),
            Represents Symbol arity (n+(types.length+1)) Delta upsilon
              (extendEnvironment (fun w => .var w) a v) (singleSubstitution A v) := by
          intro upsilon v
          cases v with
          | here => exact hA
          | there v => exact .var v
        have hafter := NumberedRewriteSyntaxProof.relatedSubstitution Symbol arity (n+(types.length+1))
          (_::Delta) Delta (arrows types tau)
          (substituteTerm body (Source.SourceMarkedBinding.liftSubstitution env)) B
          (extendEnvironment (fun v => .var v) a) (singleSubstitution A) hsingle hB
        rw [sourceBetaUnroll] at hafter
        have hsmaller : n+types.length≤n+(types.length+1) := by omega
        have hbody := NumberedRewriteSyntaxProof.budgetLowering Symbol arity (n+(types.length+1))
          (n+types.length) hsmaller Delta (arrows types tau) _ _ hafter
        have hrest := NumberedPositiveMarkProof.lowerArguments hsmaller rest V hV
        obtain ⟨R,m,htail,hR⟩ := ih Delta (extendEnvironment env a) types tau rest rfl r h
          (NumberedRewriteSyntax.substitute B (singleSubstitution A)) V hbody hrest
        have hbeta : WindowTypedTrace Symbol arity symbols S above Delta (arrows types tau) 1
            (.app (.lam B) A) (NumberedRewriteSyntax.substitute B (singleSubstitution A)) :=
          .raw (.beta B A)
        have hprefix := NumberedWindowApplicationProof.completeFunctionContext Symbol arity symbols S above Delta types tau 1 _ _ V hbeta
        refine ⟨R,1+m,?_,hR⟩
        have htransport : transportAux suffix (AuxTerm.lam B)=AuxTerm.lam B := by
          have hp : suffix=rfl := Subsingleton.elim _ _
          rw [hp]
          rfl
        rw [htransport]
        exact WindowTypedTrace.trans hprefix htail
  | ordinary f base ih =>
    intro Delta env types tau args suffix r h Q values hQ hvalues
    cases types with
    | nil => cases args; exact NumberedWindowAngleSupportProof.emptyAngle symbols S above n (.ordinary f base) env suffix r h Q values hQ
    | cons upsilon types =>
      exact ordinaryCase symbols S above n f base env (upsilon::types) tau args
        (by intro he; cases he) suffix r h Q values hQ hvalues
  | marked f output base extraTypes extras ihb ihe =>
    intro Delta env types tau args suffix r h Q values hQ hvalues
    cases types with
    | nil => cases args; exact NumberedWindowAngleSupportProof.emptyAngle symbols S above n (.marked f output base extraTypes extras) env suffix r h Q values hQ
    | cons upsilon types =>
      exact markedCase symbols S above n output f base extraTypes extras env (upsilon::types) tau args
        (by intro he; cases he) suffix r h Q values hQ hvalues
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem generalOriginalAngle : NumberedWindowAngleTargets.ActualGeneralOriginalAngle := by
  intro Symbol arity symbols S above n Gamma Delta sigma q
  exact angle symbols S above n q Delta

theorem specialApplication : NumberedWindowAngleTargets.ActualSpecialApplication := by
  intro Symbol arity symbols S above n Gamma types tau q args r h Q values hQ hvalues
  apply generalOriginalAngle Symbol arity symbols S above n Gamma Gamma _ q (fun v => .var v) types tau args rfl r h Q values
  · rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Gamma _ q]
    exact hQ
  · exact hvalues

theorem ordinaryAngleTranslation : NumberedWindowAngleTargets.ActualOrdinaryAngleTranslation := by
  intro Symbol arity symbols S above n Gamma sigma q types tau args suffix r h
  apply generalOriginalAngle Symbol arity symbols S above n Gamma Gamma sigma (embed q) (fun v => .var v)
    types tau args suffix r h (translateOriginal q) (canonicalArguments (n+types.length) args)
  · rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Gamma sigma (embed q)]
    exact NumberedRewriteSyntaxProof.ordinaryTranslation Symbol arity (n+types.length) Gamma sigma q
  · exact canonicalArgumentsRepresentation (n+types.length) args


theorem confinedSpecialApplication : NumberedWindowAngleTargets.ActualConfinedSpecialApplication := by
  intro Symbol arity symbols S hc above n Gamma types tau q args r happly Q values hQ hv hgood hvalues
  obtain ⟨R,m,hpath,hR⟩ := specialApplication Symbol arity symbols S above n Gamma types tau q args r happly Q values hQ hv
  refine ⟨R,m,hpath,hR,?_⟩
  apply NumberedWindowTracesProof.allBoundaries Symbol arity symbols S hc above Gamma m _ _
    (NumberedWindowTracesProof.typedToPacked hpath)
  exact NumberedUniverseOperationsProof.actualCompleteApplication Symbol arity (fun t => t∈S)
    (NumberedFiniteUniverse.HeadInWindow arity symbols S) hc Gamma types tau Q values hgood hvalues

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowAngleProof
