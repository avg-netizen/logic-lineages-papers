module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths
open PositiveArithmeticLeastSet SourceComputabilityFormula SourceLambdaEnvironment

theorem actualGroundDoubleLambdaSubstitution : SourceGroundDoubleLambdaSubstitutionTargets.ActualGroundDoubleLambdaSubstitution := by
  intro n arity Gamma Delta context ctx scalarOld scalarInner scalarGround scalarBoth beta tau
    hc hclosed hold hinner hground hboth theta hg he hei heg hegi body hl hfrag
  have hgl : InUniverse ctx.1.1 ctx.1.2 (.lam body) := ⟨hl.1.2.2,hl.2⟩
  have hgt : Ty.ground ∈ ctx.1.2 := hl.1.2.1
  obtain ⟨hlift,helift⟩ := SourceLambdaEnvironmentProof.actualFreshEnvironment n arity Gamma Delta
    context ctx scalarGround .ground hc hclosed hgt hground theta hg heg
  have hfurther : ∀ (upsilon : Ty) (v : Variable (.ground :: Gamma) upsilon),
      Computable n arity (beta :: .ground :: Delta) (fun x => x ∈ leastSet scalarBoth context) context upsilon
        (representativeCode ctx.1.1 ctx.1.2
          ⟨upsilon,rename (liftSubstitution theta v) (Renaming.weaken (.ground :: Delta) beta)⟩) := by
    intro upsilon v
    cases v with
    | here =>
      exact SourceInertSpineComputabilityProof.actualVariableComputable n arity (beta :: .ground :: Delta)
        context ctx scalarBoth hc hclosed hboth .ground (.there .here) hgt
    | there v => exact hegi _ v
  have hci := SourceApplicativeLambdaSubstitutionProof.actualApplicativeLambdaSubstitution n arity
    (.ground :: Gamma) (.ground :: Delta) context ctx scalarGround scalarBoth beta tau
    hc hclosed hground hboth (liftSubstitution theta) hlift helift hfurther body hgl hfrag
  have hencoded := SourceComputabilityLeastProof.actualComputabilityAccessible n arity (.ground :: Delta)
    context ctx scalarGround hc hclosed hground (.arrow beta tau) _ hci
  have hacc : Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (.ground :: Delta)) source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow beta tau,substitute (.lam body) (liftSubstitution theta)⟩) :=
    Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (.ground :: Delta) context ctx hc x y).mpr h) hencoded
  have hls := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
    (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma Delta
    (.arrow .ground (.arrow beta tau)) (.lam (.lam body)) theta hl hg
  apply SourceConditionalLambdaProof.actualConditionalLambdaComputability n arity Delta context ctx scalarOld
    hc hclosed hold .ground (.arrow beta tau) (substitute (.lam body) (liftSubstitution theta)) hls hacc
  intro a ha hca
  obtain ⟨harg,hearg⟩ := SourceLambdaEnvironmentProof.actualArgumentEnvironment n arity Gamma Delta
    context ctx (fun x => x ∈ leastSet scalarOld context) .ground theta a hg ha he hca
  have hweakarg : ∀ (upsilon : Ty) (v : Variable (.ground :: Gamma) upsilon),
      Computable n arity (beta :: Delta) (fun x => x ∈ leastSet scalarInner context) context upsilon
        (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (extend theta a v) (Renaming.weaken Delta beta)⟩) := by
    intro upsilon v
    cases v with
    | here =>
      exact (SourceGroundWeakeningProof.actualGroundComputabilityWeakening n arity Delta context ctx
        scalarOld scalarInner hc hclosed beta hold hinner a ha).mp hca
    | there v => exact hei _ v
  have hinstance := SourceApplicativeLambdaSubstitutionProof.actualApplicativeLambdaSubstitution n arity
    (.ground :: Gamma) Delta context ctx scalarOld scalarInner beta tau hc hclosed hold hinner
    (extend theta a) harg hearg hweakarg body hgl hfrag
  rw [SourceLambdaEnvironmentProof.actualExtendedBetaIdentity (Fin n) arity Gamma Delta .ground (.arrow beta tau) theta (.lam body) a]
  exact hinstance

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundDoubleLambdaSubstitutionProof
