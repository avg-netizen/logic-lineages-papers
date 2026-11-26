module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceFullSubstitution SourceLambdaEnvironment
open SourceFullSubstitutionSupportProof

theorem actualWindowComputableSubstitution : SourceFullSubstitutionTargets.ActualWindowComputableSubstitution := by
  intro n arity Gamma Delta context ctx scalar hc hclosed hcal rank hrank theta hg he tau q
  revert theta
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args =>
      ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
      NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
        (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
      WindowComputableEnvironment n arity Gamma Delta context ctx scalar theta →
      NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
        (HeadInWindow arity ctx.1.1 ctx.1.2) args →
      ∀ p ∈ argumentList (substituteArguments args theta),
        Computable n arity Delta (fun x => x ∈ leastSet scalar context) context p.1
          (representativeCode ctx.1.1 ctx.1.2 p))
  case var v =>
    intro theta hg he hq
    exact he _ v hq.1
  case bottom tau =>
    intro theta hg he hq
    exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Delta context ctx scalar
      hc hclosed hcal tau hq.1
  case app f a ihf iha =>
    intro theta hg he hq
    have hfg : InUniverse ctx.1.1 ctx.1.2 f := ⟨hq.1.2.1,hq.2.1⟩
    have hag : InUniverse ctx.1.1 ctx.1.2 a := ⟨hq.1.2.2,hq.2.2⟩
    have hfs := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ f theta hfg hg
    have has := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ a theta hag hg
    exact SourceConditionalLambdaSupportProof.applicationComputable n arity Delta context ctx scalar
      hc hclosed _ _ (substitute f theta) (substitute a theta) hfs has
      (ihf theta hg he hfg) (iha theta hg he hag)
  case lam body ih =>
    intro theta hg he hq
    have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hq.1.2.2,hq.2⟩
    have hls := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ (.lam body) theta hq hg
    apply SourceLambdaComputabilityProof.actualLambdaComputability n arity Delta context ctx scalar
      hc hclosed hcal _ _ (substitute body (liftSubstitution theta)) hls
    intro a ha hca
    obtain ⟨harg,hearg⟩ := extendWindowEnvironment theta a hg ha he hca
    rw [SourceLambdaEnvironmentProof.actualExtendedBetaIdentity (Fin n) arity _ Delta _ _ theta body a]
    exact ih (extend theta a) harg hearg hb
  case ordinary f base ih =>
    intro theta hg he hq
    have hqs := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _ (.ordinary f base) theta hq hg
    exact SourceRankedConstructorComputabilityProof.actualOrdinaryConstructorComputable n arity Delta
      context ctx scalar hc hclosed hcal rank hrank f (substituteArguments base theta) hqs
      (ih theta hg he ⟨hq.1.2,hq.2.2⟩)
  case numbered k f tau base types extras ihb ihe =>
    intro theta hg he hq
    have hqs := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) _ Delta _
      (.numbered k f tau base types extras) theta hq hg
    apply SourceRankedConstructorComputabilityProof.actualNumberedConstructorComputable n arity Delta
      context ctx scalar hc hclosed hcal rank hrank k f tau (substituteArguments base theta) types
      (substituteArguments extras theta) hqs
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ihb theta hg he ⟨hq.1.2.1,hq.2.2.1⟩ p hp
    · exact ihe theta hg he ⟨hq.1.2.2,hq.2.2.2⟩ p hp
  case nil Gamma theta hg he hargs p hp =>
    exact False.elim (List.not_mem_nil hp)
  case cons Gamma sigma types q rest ihq ihr theta hg he hargs p hp =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ihq theta hg he ⟨hargs.1.1,hargs.2.1⟩
    · exact ihr theta hg he ⟨hargs.1.2,hargs.2.2⟩ p hp

theorem actualFullComputableSubstitution : SourceFullSubstitutionTargets.ActualFullComputableSubstitution := by
  intro n arity Gamma Delta context ctx scalar hc hclosed hcal rank hrank theta hg he tau q hq
  exact actualWindowComputableSubstitution n arity Gamma Delta context ctx scalar hc hclosed hcal
    rank hrank theta hg (fun tau v _ => he tau v) tau q hq

theorem actualArgumentComputableSubstitution : SourceFullSubstitutionTargets.ActualArgumentComputableSubstitution := by
  intro n arity Gamma Delta context ctx scalar hc hclosed hcal rank hrank theta hg he types args hargs
  induction types with
  | nil =>
    cases args
    intro p hp
    exact False.elim (List.not_mem_nil hp)
  | cons tau types ih =>
    cases args with
    | cons q rest =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact actualWindowComputableSubstitution n arity Gamma Delta context ctx scalar hc hclosed hcal
          rank hrank theta hg he tau q ⟨hargs.1.1,hargs.2.1⟩
      · exact ih rest ⟨hargs.1.2,hargs.2.2⟩ p hp

theorem actualAllTermComputable : SourceFullSubstitutionTargets.ActualAllTermComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal rank hrank tau q hq
  have hg : NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) (fun v => AuxTerm.var (arity := arity) (Gamma := Gamma) v) := by
    intro upsilon v ht
    exact ⟨ht,trivial⟩
  have he : WindowComputableEnvironment n arity Gamma Gamma context ctx scalar (fun v => AuxTerm.var v) := by
    intro upsilon v ht
    exact SourceInertSpineComputabilityProof.actualVariableComputable n arity Gamma context ctx scalar
      hc hclosed hcal upsilon v ht
  have h := actualWindowComputableSubstitution n arity Gamma Gamma context ctx scalar hc hclosed hcal
    rank hrank (fun v => AuxTerm.var v) hg he tau q hq
  rw [substituteIdentity] at h
  exact h

theorem actualAllTermLeast : SourceFullSubstitutionTargets.ActualAllTermLeast := by
  intro n arity Gamma context ctx scalar hc hclosed hcal rank hrank tau q hq
  exact SourceComputabilityLeastProof.actualComputabilityLeast n arity Gamma context ctx scalar
    hc hclosed hcal tau _ (actualAllTermComputable n arity Gamma context ctx scalar
      hc hclosed hcal rank hrank tau q hq)

theorem actualAllTermAccessible : SourceFullSubstitutionTargets.ActualAllTermAccessible := by
  intro n arity Gamma context ctx scalar hc hclosed hcal rank hrank tau q hq
  exact SourceComputabilityLeastProof.actualComputabilityAccessible n arity Gamma context ctx scalar
    hc hclosed hcal tau _ (actualAllTermComputable n arity Gamma context ctx scalar
      hc hclosed hcal rank hrank tau q hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFullSubstitutionProof
