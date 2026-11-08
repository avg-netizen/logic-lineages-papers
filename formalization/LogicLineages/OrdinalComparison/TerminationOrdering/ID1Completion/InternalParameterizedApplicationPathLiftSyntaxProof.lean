module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalParameterizedPathChecker InternalParameterizedApplicationPathLift InternalClosedPrograms
open InternalParameterizedPathCheckerSyntaxProof
open InternalApplicationPathLiftSyntaxProof
  (parametersExpand vertexInputsRename vertexInputsSubst vertexAtRename invariantAtRename
    liftedEdgeAtRename mappedAtRename vertexAtSubst)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalFiniteBlocksSubstitutionProof InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem inputsRename {α β : Type} (edge : Program 4) (vertex invariant : Program 5)
    (positive : Bool) (ps : Parameters α) (x y code out other mapped : OTerm α) (j : α → β) :
    (inputs edge vertex invariant positive ps x y code out other mapped).relabel j =
      inputs edge vertex invariant positive (fun i => (ps i).relabel j)
        (x.relabel j) (y.relabel j) (code.relabel j) (out.relabel j) (other.relabel j) (mapped.relabel j) := by
  change (invariantAt invariant ps x).relabel j ⊓
    ((checkerGraph edge positive (suc z) x y code (ps 0)).relabel j ⊓
      ((vertexAt vertex ps out x).relabel j ⊓
        ((vertexAt vertex ps other y).relabel j ⊓ (mappedAt vertex ps mapped code).relabel j))) = _
  rw [invariantAtRename,checkerRename,vertexAtRename,vertexAtRename,mappedAtRename,
    InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  rfl

theorem checkerSubst {α β : Type} (edge : Program 4) (positive : Bool)
    (out x y code parameter : OTerm α) (ts : α → OTerm β) :
    (checkerGraph edge positive out x y code parameter).subst (fun a => emb (ts a)) =
      checkerGraph edge positive (out.subst ts) (x.subst ts) (y.subst ts) (code.subst ts) (parameter.subst ts) := by
  unfold checkerGraph
  rw [programSubst]
  simp only [quadruple,consTermSubst,emptySubst]

theorem inputsSubst {α β : Type} (edge : Program 4) (vertex invariant : Program 5)
    (positive : Bool) (ps : Parameters α) (x y code out other mapped : OTerm α) (ts : α → OTerm β) :
    (inputs edge vertex invariant positive ps x y code out other mapped).subst (fun a => emb (ts a)) =
      inputs edge vertex invariant positive (fun i => (ps i).subst ts)
        (x.subst ts) (y.subst ts) (code.subst ts) (out.subst ts) (other.subst ts) (mapped.subst ts) := by
  unfold inputs invariantAt mappedAt vertexAt
    InternalApplicationPathLift.invariantAt InternalApplicationPathLift.mappedAt
  simp only [conjunctionSubst,vertexAtSubst,checkerSubst,programSubst,consTermSubst,
    InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]

theorem rowSubst {α β : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) (ts : α → OTerm β) :
    (row edge vertex invariant ps code).subst (fun a => emb (ts a)) =
      row edge vertex invariant (fun i => (ps i).subst ts) (code.subst ts) := by
  unfold row matrix
  rw [allBlockSubst,liftedEmbedding,InternalAdditionLawsProof.impSubst,inputsSubst]
  unfold pathGraph
  rw [checkerSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr,
    InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]

theorem rowRename {α β : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) (j : α → β) :
    (row edge vertex invariant ps code).relabel j =
      row edge vertex invariant (fun i => (ps i).relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row edge vertex invariant ps code).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {α : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code x y out other mapped : OTerm α) :
    (matrix edge vertex invariant ps code).subst
      (Sum.elim Term.var (fun i => emb (![x,y,out,other,mapped] i))) =
      (inputs edge vertex invariant false ps x y code out other mapped).imp (pathGraph edge out other mapped (ps 0)) := by
  have he : (Sum.elim Term.var (fun i => emb (![x,y,out,other,mapped] i))) =
      (fun a => emb (Sum.elim Term.var ![x,y,out,other,mapped] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,InternalAdditionLawsProof.impSubst,inputsSubst]
  unfold pathGraph
  rw [checkerSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr,
    InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]
  rfl

theorem rowAtCode {α : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) :
    InternalListInduction.atCode
      (row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr 0))) code =
        row edge vertex invariant ps code := by
  rw [InternalListInduction.atCode,instantiate,bindEmbedding,rowSubst]
  simp only [liftBind,varBind]

theorem rowAtIndex {α : Type} (edge : Program 4) (vertex invariant : Program 5)
    (ps : Parameters α) (index : Fin 3) :
    InternalListInduction.atIndex
      (row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr 0))) index =
        row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr index)) := by
  rw [InternalListInduction.atIndex,rowRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSyntaxProof
