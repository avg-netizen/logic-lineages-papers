module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalComputabilityDownwardProof (edgeCases)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open InternalRecursionGraphSyntaxProof (liftSubst)
open InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open InternalRecursionGraphStepSyntaxProof
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalEdgeExposureTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem witnessSubst {beta : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target : OTerm alpha) (ts : alpha → OTerm beta) :
    (Witness q context source target).subst (fun a => emb (ts a)) =
      Witness q context (source.subst ts) (target.subst ts) := by
  unfold Witness
  rw [existsSubst,liftedEmbedding]
  unfold Matrix
  simp only [conjunctionSubst,Erasure.VariableSourceErasureSyntaxProof.certificateSubst,
    Erasure.PositiveSourceExposureSyntaxProof.witnessSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem witnessRename {beta : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target : OTerm alpha) (j : alpha → beta) :
    (Witness q context source target).relabel j =
      Witness q context (source.relabel j) (target.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Witness q context source target).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem matrixInstance (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target path : OTerm alpha) :
    instantiate (Matrix q context source target) (emb path) =
      InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false
          context source target path ⊓
        Erasure.PositiveSourceExposureTargets.Witness q context source target path := by
  rw [instantiate,bindEmbedding]
  unfold Matrix
  simp only [conjunctionSubst,Erasure.VariableSourceErasureSyntaxProof.certificateSubst,
    Erasure.PositiveSourceExposureSyntaxProof.witnessSubst,liftBind,varBind]

theorem witnessIntro (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target path : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false
        context source target path)))
    (hr : Nonempty (Derivation body Delta
      (Erasure.PositiveSourceExposureTargets.Witness q context source target path))) :
    Nonempty (Derivation body Delta (Witness q context source target)) := by
  obtain ⟨h⟩ := andIntro hc hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb path)
  rw [matrixInstance]
  exact h

/-- The OLD source R edge binds its own path certificate. The first raw W
and every associated computation are then derived at that same actual path. -/
theorem expose (q : GlobalSourcePackage.Inputs) (context : Nat)
    (source target : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 q.window (numeral 1) (numeral context))))
    (he : Nonempty (Derivation body Delta
      (InternalAccessibilityRules.edge (GlobalSourcePackage.source q) false context source target))) :
    Nonempty (Derivation body Delta (Witness q context source target)) := by
  apply edgeCases (GlobalSourcePackage.source q) context source target _ he
  intro beta j Theta path hj hc
  rw [witnessRename]
  have hw' := renameInto hw j Theta hj
  simp only [graph1Rename,numeralRename] at hw'
  have hr := Erasure.PositiveSourceExposureProof.expose q context
    (source.relabel j) (target.relabel j) path hw' hc
  exact witnessIntro q context (source.relabel j) (target.relabel j) path hc hr

theorem actualOriginalEdgeFirstRawStep : ActualOriginalEdgeFirstRawStep := by
  intro p H G W P body alpha Delta context source target
  let q := preparedKernelFinalInputs p H G W P
  let A := graph1 q.window (numeral 1) (numeral context) ⊓
    InternalAccessibilityRules.edge (GlobalSourcePackage.source q) false context source target
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := expose q context source target (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalEdgeExposureProof
