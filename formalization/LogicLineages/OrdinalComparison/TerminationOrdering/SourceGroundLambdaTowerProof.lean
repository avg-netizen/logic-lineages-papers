module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticLeastSet SourceComputabilityFormula SourceLambdaEnvironment
open SourceGroundContextTower SourceGroundContextTowerProof SourceGroundLambdaTower SourceGroundLambdaTowerSupportProof

theorem actualGroundLambdaTowerSubstitution : SourceGroundLambdaTowerTargets.ActualGroundLambdaTowerSubstitution := by
  intro n arity Gamma Delta context ctx k scalar hc hclosed
  revert Gamma Delta scalar
  induction k with
  | zero =>
    intro Gamma Delta scalar hcal theta hg he tau q hq hf
    apply SourceApplicativeSubstitutionProof.actualApplicativeComputableSubstitution n arity Gamma Delta
      context ctx (scalar 0) hc hclosed (hcal 0 (Nat.le_refl _)) theta hg _ tau q hq hf
    intro upsilon v
    have hv := he 0 (Nat.le_refl _) upsilon v
    rw [(actualGroundRenamingEquations (Fin n) arity Delta upsilon (theta v)).1] at hv
    exact hv
  | succ k ih =>
    intro Gamma Delta scalar hcal theta hg he tau q hq hf
    cases q with
    | var v => exact False.elim hf
    | bottom t => exact False.elim hf
    | app f a => exact False.elim hf
    | ordinary f base => exact False.elim hf
    | numbered label f t base types extras => exact False.elim hf
    | lam body =>
      obtain ⟨hs,hf⟩ := hf
      cases hs
      have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hq.1.2.2,hq.2⟩
      have hgt : Ty.ground ∈ ctx.1.2 := hq.1.2.1
      have hshift : ∀ j : Nat, j ≤ k → PositiveArithmeticAccessibility.Calibrates (scalar (j + 1)) context
          (encodedScalar n arity (groundContext j (.ground :: Delta)) context)
          (PositiveArithmeticOperators.encodedR n arity (groundContext j (.ground :: Delta)) context) := by
        intro j hj
        rw [contextShift]
        exact hcal (j + 1) (Nat.succ_le_succ hj)
      have hlift : NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
          (HeadInWindow arity ctx.1.1 ctx.1.2) (liftSubstitution (sigma := Ty.ground) theta) :=
        NumberedUniverseBindingProof.liftGood _ _ theta hg
      have hshiftImages : ∀ (j : Nat), j ≤ k → ∀ (upsilon : Ty) (v : Variable (.ground :: Gamma) upsilon),
          Computable n arity (groundContext j (.ground :: Delta))
            (fun x => x ∈ leastSet (scalar (j + 1)) context) context upsilon
            (representativeCode ctx.1.1 ctx.1.2
              ⟨upsilon,rename (liftSubstitution theta v) (groundRenaming j (.ground :: Delta))⟩) := by
        intro j hj upsilon v
        cases v with
        | here =>
          exact SourceInertSpineComputabilityProof.actualVariableComputable n arity
            (groundContext j (.ground :: Delta)) context ctx (scalar (j + 1)) hc hclosed (hshift j hj)
            .ground (groundRenaming j (.ground :: Delta) .here) hgt
        | there v =>
          exact (shiftedRenamingProperty (theta v) j
            (fun Xi r => Computable n arity Xi (fun x => x ∈ leastSet (scalar (j + 1)) context)
              context _ (representativeCode ctx.1.1 ctx.1.2 ⟨_,r⟩))).mpr
            (he (j + 1) (Nat.succ_le_succ hj) _ v)
      have hcb := ih (.ground :: Gamma) (.ground :: Delta) (fun j => scalar (j + 1)) hshift
        (liftSubstitution theta) hlift hshiftImages _ body hb hf
      have hencoded := SourceComputabilityLeastProof.actualComputabilityAccessible n arity (.ground :: Delta)
        context ctx (scalar 1) hc hclosed (hcal 1 (Nat.succ_le_succ (Nat.zero_le k))) _ _ hcb
      have hacc : Acc (fun successor source => PositivePath
          (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (.ground :: Delta)) source successor)
          (representativeCode ctx.1.1 ctx.1.2 ⟨_,substitute body (liftSubstitution theta)⟩) :=
        Subrelation.accessible (fun {y x} h =>
          (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (.ground :: Delta) context ctx hc x y).mpr h) hencoded
      have hls := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
        (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma Delta _ (.lam body) theta hq hg
      apply SourceConditionalLambdaProof.actualConditionalLambdaComputability n arity Delta context ctx (scalar 0)
        hc hclosed (hcal 0 (Nat.zero_le _)) .ground _ (substitute body (liftSubstitution theta)) hls hacc
      intro a ha hca
      have he0 : ∀ (upsilon : Ty) (v : Variable Gamma upsilon), Computable n arity Delta
          (fun x => x ∈ leastSet (scalar 0) context) context upsilon (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,theta v⟩) := by
        intro upsilon v
        have hv := he 0 (Nat.zero_le _) upsilon v
        rw [(actualGroundRenamingEquations (Fin n) arity Delta upsilon (theta v)).1] at hv
        exact hv
      obtain ⟨harg,_⟩ := SourceLambdaEnvironmentProof.actualArgumentEnvironment n arity Gamma Delta
        context ctx (fun x => x ∈ leastSet (scalar 0) context) .ground theta a hg ha he0 hca
      have hargImages : ∀ (j : Nat), j ≤ k → ∀ (upsilon : Ty) (v : Variable (.ground :: Gamma) upsilon),
          Computable n arity (groundContext j Delta) (fun x => x ∈ leastSet (scalar j) context) context upsilon
            (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (extend theta a v) (groundRenaming j Delta)⟩) := by
        intro j hj upsilon v
        cases v with
        | here =>
          exact (actualGroundTowerComputability n arity Delta context ctx j scalar hc hclosed
            (fun i hi => hcal i (Nat.le_trans hi (Nat.le_trans hj (Nat.le_succ k)))) a ha).mp hca
        | there v => exact he j (Nat.le_trans hj (Nat.le_succ k)) _ v
      have hinstance := ih (.ground :: Gamma) Delta scalar
        (fun j hj => hcal j (Nat.le_trans hj (Nat.le_succ k))) (extend theta a) harg hargImages _ body hb hf
      rw [SourceLambdaEnvironmentProof.actualExtendedBetaIdentity (Fin n) arity Gamma Delta .ground _ theta body a]
      exact hinstance

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerProof
