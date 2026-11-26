module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof (programSubst consTermSubst emptySubst)
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb sucSubst zSubst)
open OriginalContextInsertionSyntaxProof (blockSubst)
open UniformCertificateCompletion PositiveSourceExposureTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsSubst {beta : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ys : Fin 11 → OTerm alpha) (ts : alpha → OTerm beta) :
    (Fields q context f g path ys).subst (fun a => emb (ts a)) =
      Fields q context (f.subst ts) (g.subst ts) (path.subst ts) (fun i => (ys i).subst ts) := by
  simp only [Fields,selectors,stepAccepted,InternalParameterizedCanonicalResultFold.foldGraph,
    InternalParameterizedPathChecker.pathGraph,InternalParameterizedPathChecker.checkerGraph,
    InternalParameterizedPathChecker.quadruple,graph1,graph2,graph3,graph4,
    programSubst,consTermSubst,emptySubst,conjunctionSubst,
    InternalAccessibilityRulesSyntaxProof.numeralSubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem witnessSubst {beta : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ts : alpha → OTerm beta) :
    (Witness q context f g path).subst (fun a => emb (ts a)) =
      Witness q context (f.subst ts) (g.subst ts) (path.subst ts) := by
  unfold Witness Matrix
  rw [blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem witnessRename {beta : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (j : alpha → beta) :
    (Witness q context f g path).relabel j =
      Witness q context (f.relabel j) (g.relabel j) (path.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Witness q context f g path).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ys : Fin 11 → OTerm alpha) :
    (Matrix q context f g path).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      Fields q context f g path ys := by
  have he : (Sum.elim Term.var (fun i => emb (ys i))) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold Matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem witnessIntro (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ys : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (Fields q context f g path ys))) :
    Nonempty (Derivation body Delta (Witness q context f g path)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 11 Delta (Matrix q context f g path)
    (fun i => emb (ys i))
  rw [matrixWitness]
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureSyntaxProof
