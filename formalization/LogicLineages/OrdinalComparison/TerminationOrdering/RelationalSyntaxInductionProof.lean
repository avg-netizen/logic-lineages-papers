module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxFunctionalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxInductionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment
open CoherentConstructorLattice ConstructorInputLogicalRelation ConfinedStructuralInterpretation OriginalSpineActions
open RelatedEnvironments ActualValueLogicalRelation SourceConstructorIteration RelationalSyntax

/-- Actual mutual MarkedTerm/Arguments syntax induction pays EVERY body/scanner
hypothesis of the lambda constructor. No fundamental theorem is an input. -/
theorem actualJointFundamental : RelationalSyntaxTargets.ActualJointFundamental := by
  intro Symbol inst arity I above dec
  letI : DecidableRel above := dec
  let M := limit I above
  have hM : FamilySound I above M := ActualConstructorFamilySoundnessProof.actualLimitSound Symbol inst arity I above dec
  have termCore : ∀ {Gamma : List Ty} {sigma : Ty} (q : MarkedTerm Symbol arity Gamma sigma)
      (hq : Confined I q),EvaluationRelated I above M ⟨q,hq⟩ ∧ ScannerRelated I above M ⟨q,hq⟩ := by
    intro Gamma sigma q
    induction q using MarkedTerm.rec
      (motive_2 := fun Gamma types args => ∀ ha : ArgumentsConfined I args,ArgumentsRelated I above M args ha) with
    | var v =>
      intro hq
      exact RelationalSyntaxVariableProof.variableCase above M v hq
    | lam body ih =>
      intro hq
      let bodyC : ConfinedTerm I _ _ := ⟨body,⟨hq.1.2.2,hq.2⟩⟩
      have H := ih bodyC.property
      exact RelationalSyntaxLambdaProof.lambdaCase above M bodyC hq H.1 H.2
    | ordinary f base ih =>
      intro hq
      let hb : ArgumentsConfined I base := ⟨hq.1.2,hq.2.2⟩
      exact RelationalSyntaxFunctionalProof.ordinaryCase above M hM f base hb hq (ih hb)
    | marked f out base extraTypes extras ihb ihe =>
      intro hq
      let hb : ArgumentsConfined I base := ⟨hq.1.2.1,hq.2.2.1⟩
      let hx : ArgumentsConfined I extras := ⟨hq.1.2.2,hq.2.2.2⟩
      exact RelationalSyntaxFunctionalProof.markedCase above M hM f out base extraTypes extras hb hx hq
        (ihb hb) (ihe hx)
    | nil =>
      intros
      rename_i ha
      unfold ArgumentsRelated
      intro P rho s hr i
      exact Fin.elim0 i
    | cons q rest ihq ihr =>
      intros
      rename_i ha
      unfold ArgumentsRelated
      intro P rho s hr i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (ihq ⟨ha.1.1,ha.2.1⟩).1 P rho s hr
      · exact ihr ⟨ha.1.2,ha.2.2⟩ P rho s hr j
  constructor
  · intro Gamma sigma q
    exact termCore q.val q.property
  · intro Gamma types args ha
    induction types with
    | nil => cases args; intro P rho s hr i; exact Fin.elim0 i
    | cons tau types ih =>
      cases args with
      | cons q rest =>
        intro P rho s hr i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (termCore q ⟨ha.1.1,ha.2.1⟩).1 P rho s hr
        · exact ih rest ⟨ha.1.2,ha.2.2⟩ P rho s hr j

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxInductionProof
