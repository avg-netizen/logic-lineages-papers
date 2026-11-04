module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilitySupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedBottomAccessibilitySupportProof

theorem actualBottomPrimaryRigid : NumberedBottomAccessibilityTargets.ActualBottomPrimaryRigid := by
  intro Symbol arity symbols S Gamma tau q h
  exact bottomViewRigid q tau (primaryBottomView h).symm

theorem actualBottomStepTerminal : NumberedBottomAccessibilityTargets.ActualBottomStepTerminal := by
  intro Symbol arity symbols S above Gamma tau q h
  cases h with
  | bottom q h => exact h rfl

theorem actualBottomPositiveTerminal : NumberedBottomAccessibilityTargets.ActualBottomPositiveTerminal := by
  intro n arity symbols S hc above Gamma tau ht
  have hb : InUniverse symbols S (AuxTerm.bottom tau : AuxTerm (Fin n) arity Gamma tau) := ⟨ht, trivial⟩
  apply noPositiveOfNoEdge
  intro y hedge
  obtain ⟨rho,q,r,hq,hstep,hcode,hr⟩ := hedge
  have hequiv := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma) ⟨rho,q⟩ hb hq).mp hcode.symm
  have he := actualBottomPrimaryRigid (Fin n) arity symbols S Gamma tau ⟨rho,q⟩ hequiv
  have htype : rho = tau := congrArg Sigma.fst he
  cases htype
  have hqeq : q = AuxTerm.bottom tau := by injection he
  subst q
  exact actualBottomStepTerminal (Fin n) arity symbols S above Gamma tau r hstep

theorem actualBottomAccessibleLeast : NumberedBottomAccessibilityTargets.ActualBottomAccessibleLeast := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau ht
  let value := representativeCode ctx.1.1 ctx.1.2 (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma)
  have hacc : Acc (fun successor source => encodedR n arity Gamma context source successor) value := by
    refine Acc.intro _ ?_
    intro y hy
    exact False.elim (actualBottomPositiveTerminal n arity ctx.1.1 ctx.1.2 hclosed
      (NumberedCopyCertificate.tableAbove ctx.2) Gamma tau ht y
      ((SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc value y).mp hy))
  have hcarrier : encodedScalar n arity Gamma context value := by
    refine ⟨ctx,hc,?_⟩
    apply (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma value).mpr
    exact ⟨⟨tau,AuxTerm.bottom tau⟩, ⟨ht,trivial⟩, rfl⟩
  refine ⟨hacc, ?_⟩
  exact (PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalar context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcal
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity Gamma context ⟨ctx,hc,hclosed⟩) value).mpr
    ⟨hcarrier,hacc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityProof
