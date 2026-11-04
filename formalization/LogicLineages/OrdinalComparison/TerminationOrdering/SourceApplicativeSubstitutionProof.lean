module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitutionProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open SourceApplicativeSubstitution

theorem actualApplicativeComputableSubstitution : SourceApplicativeSubstitutionTargets.ActualApplicativeComputableSubstitution := by
  intro n arity Gamma Delta context ctx scalar hc hclosed hcal theta hg he tau q
  revert theta
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case var v =>
    intro theta hg he hq hf
    exact he _ v
  case bottom tau =>
    intro theta hg he hq hf
    exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Delta context ctx scalar
      hc hclosed hcal tau hq.1
  case app f a ihf iha =>
    intro theta hg he hq hf
    have hfg : InUniverse ctx.1.1 ctx.1.2 f := ⟨hq.1.2.1,hq.2.1⟩
    have hag : InUniverse ctx.1.1 ctx.1.2 a := ⟨hq.1.2.2,hq.2.2⟩
    have hfs := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ f theta hfg hg
    have has := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ a theta hag hg
    exact SourceConditionalLambdaSupportProof.applicationComputable n arity Delta context ctx scalar
      hc hclosed _ _ (substitute f theta) (substitute a theta) hfs has
      (ihf theta hg he hfg hf.1) (iha theta hg he hag hf.2)
  case lam body ih => intro theta hg he hq hf; exact False.elim hf
  case ordinary f base ih => intro theta hg he hq hf; exact False.elim hf
  case numbered k f tau base types extras ihb ihe => intro theta hg he hq hf; exact False.elim hf
  case nil => trivial
  case cons => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitutionProof
