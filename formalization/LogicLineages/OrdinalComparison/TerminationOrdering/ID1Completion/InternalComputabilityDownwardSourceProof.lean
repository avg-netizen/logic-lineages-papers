module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalComputabilityDownwardProof InternalComputabilityApplicationSyntaxProof
open GuardedSourceSyntaxProof GammaGuardedSourceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem domainLiteral {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) :
    ApplicationGuarded.domain comp context sigma tau f a = domain comp context sigma tau f a := by
  unfold ApplicationGuarded.domain domain
  rw [literalTypedGraph,literalTypedGraph,literalGuardGraph]
  rfl

theorem existsLiteral {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) :
    ApplicationGuarded.existsApplication comp context sigma tau f a =
      applicationExists comp context sigma tau f a := by
  unfold ApplicationGuarded.existsApplication applicationExists
  congr 1
  exact applicationLiteral comp sigma tau (numeral context) _ _ _

/-- Use one existing calibrated package, retaining its exact checker Programs.
Only the numerical path Program is selected here; its symbolic correctness is
the explicit hypothesis of the returned implication, never inferred from eval. -/
theorem actualUniformSourceDownwardReduction :
    InternalComputabilityDownwardTargets.ActualUniformSourceDownwardReduction := by
  intro n arity
  obtain ⟨src,comp,result,hs,hc,_,hclosure,hguard⟩ :=
    InternalComputabilityApplicationSourceProof.actualUniformSourceComputableApplication n arity
  obtain ⟨lift,hlift⟩ := ApplicationCertificateLiftPathPrimitiveProof.actualProgramWitness n arity
  refine ⟨src,comp,lift,hs,hc,hlift,?_⟩
  intro symbols S table hclosed
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have rules : ArithmeticRules src comp context := by
    constructor
    · intro α tau f g
      have h := (hclosure symbols S table hclosed α).1 (numeral (typeNumber tau)) f g
      simpa only [literalTypedGraph,GuardedSource.literalR,typed,edge,edgeProgram] using h
    · intro α tau f g a
      have h := hguard context α (numeral (typeNumber tau)) f g a
      simpa only [literalTypedGraph,literalGuardGraph,GuardedSource.literalR,
        typed,guarded,edge,edgeProgram] using h
    · intro α sigma tau f a
      have h := (hclosure symbols S table hclosed α).2.2.1 sigma tau f a
      simpa only [domainLiteral,existsLiteral] using h
  refine ⟨rules,?_⟩
  intro hcert tau α f g
  let P := computable comp tau (numeral context) f ⊓ edge src false context f g
  have hp : Derivation (SourcePresentation.sourceBody src context) [P] P :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := actualOriginalComputabilityDownward src comp context rules
    (actualOriginalCertifiedLiftReduction src comp lift context hcert) tau α [P] f g
    ⟨Derivation.conjunctionLeft hp⟩ ⟨Derivation.conjunctionRight hp⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSourceProof
