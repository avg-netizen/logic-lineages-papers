module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalPathChecker InternalApplicationPathLift InternalClosedPrograms
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof
open InternalRecursionGraphSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalFiniteBlocksSubstitutionProof InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem parametersExpand {α : Type} (ps : Parameters α) :
    InternalApplicationPathMap.parameters (ps 0) (ps 1) (ps 2) (ps 3) = ps := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem vertexInputsRename {α β : Type} (ps : Parameters α) (x : OTerm α) (j : α → β) :
    (fun i => (vertexInputs ps x i).relabel j) =
      vertexInputs (fun i => (ps i).relabel j) (x.relabel j) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i

theorem vertexInputsSubst {α β : Type} (ps : Parameters α) (x : OTerm α) (ts : α → OTerm β) :
    (fun i => (vertexInputs ps x i).subst ts) =
      vertexInputs (fun i => (ps i).subst ts) (x.subst ts) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i

theorem vertexAtRename {α β : Type} (vertex : Program 5) (ps : Parameters α)
    (out x : OTerm α) (j : α → β) :
    (vertexAt vertex ps out x).relabel j =
      vertexAt vertex (fun i => (ps i).relabel j) (out.relabel j) (x.relabel j) := by
  rw [vertexAt,programRename,vertexInputsRename]
  rfl

theorem invariantAtRename {α β : Type} (invariant : Program 5) (ps : Parameters α)
    (x : OTerm α) (j : α → β) :
    (invariantAt invariant ps x).relabel j =
      invariantAt invariant (fun i => (ps i).relabel j) (x.relabel j) := by
  unfold invariantAt
  rw [vertexAtRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]

theorem liftedEdgeAtRename {α β : Type} (ps : Parameters α) (out c : OTerm α) (j : α → β) :
    (liftedEdgeAt ps out c).relabel j =
      liftedEdgeAt (fun i => (ps i).relabel j) (out.relabel j) (c.relabel j) := by
  unfold liftedEdgeAt
  rw [graph4Rename]

theorem mappedAtRename {α β : Type} (vertex : Program 5) (ps : Parameters α)
    (out code : OTerm α) (j : α → β) :
    (mappedAt vertex ps out code).relabel j =
      mappedAt vertex (fun i => (ps i).relabel j) (out.relabel j) (code.relabel j) := by
  rw [mappedAt,programRename,consTermRename]
  rfl

theorem checkerRename {α β : Type} (edge : Program 3) (positive : Bool)
    (out x y code : OTerm α) (j : α → β) :
    (checkerGraph edge positive out x y code).relabel j =
      checkerGraph edge positive (out.relabel j) (x.relabel j) (y.relabel j) (code.relabel j) :=
  InternalPathCheckerSyntaxProof.checkerRename edge positive out x y code j

theorem pathRename {α β : Type} (edge : Program 3) (x y code : OTerm α) (j : α → β) :
    (pathGraph edge x y code).relabel j = pathGraph edge (x.relabel j) (y.relabel j) (code.relabel j) := by
  unfold pathGraph
  rw [checkerRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]

theorem positiveRename {α β : Type} (edge : Program 3) (x y code : OTerm α) (j : α → β) :
    (positiveGraph edge x y code).relabel j = positiveGraph edge (x.relabel j) (y.relabel j) (code.relabel j) := by
  unfold positiveGraph
  rw [checkerRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]

theorem edgeRename {α β : Type} (edge : Program 3) (x y c : OTerm α) (j : α → β) :
    (edgeGraph edge x y c).relabel j = edgeGraph edge (x.relabel j) (y.relabel j) (c.relabel j) :=
  InternalPathCheckerSyntaxProof.edgeRename edge x y c j

theorem inputsRename {α β : Type} (edge : Program 3) (vertex invariant : Program 5)
    (positive : Bool) (ps : Parameters α) (x y code out other mapped : OTerm α) (j : α → β) :
    (inputs edge vertex invariant positive ps x y code out other mapped).relabel j =
      inputs edge vertex invariant positive (fun i => (ps i).relabel j)
        (x.relabel j) (y.relabel j) (code.relabel j) (out.relabel j) (other.relabel j) (mapped.relabel j) := by
  change (invariantAt invariant ps x).relabel j ⊓
    ((checkerGraph edge positive (suc z) x y code).relabel j ⊓
      ((vertexAt vertex ps out x).relabel j ⊓
        ((vertexAt vertex ps other y).relabel j ⊓ (mappedAt vertex ps mapped code).relabel j))) = _
  rw [invariantAtRename,checkerRename,vertexAtRename,vertexAtRename,mappedAtRename,
    InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  rfl

theorem vertexAtSubst {α β : Type} (vertex : Program 5) (ps : Parameters α)
    (out x : OTerm α) (ts : α → OTerm β) :
    (vertexAt vertex ps out x).subst (fun a => emb (ts a)) =
      vertexAt vertex (fun i => (ps i).subst ts) (out.subst ts) (x.subst ts) := by
  rw [vertexAt,programSubst,vertexInputsSubst]
  rfl

theorem checkerSubst {α β : Type} (edge : Program 3) (positive : Bool)
    (out x y code : OTerm α) (ts : α → OTerm β) :
    (checkerGraph edge positive out x y code).subst (fun a => emb (ts a)) =
      checkerGraph edge positive (out.subst ts) (x.subst ts) (y.subst ts) (code.subst ts) := by
  unfold checkerGraph
  rw [programSubst]
  simp only [triple,consTermSubst,emptySubst]

theorem inputsSubst {α β : Type} (edge : Program 3) (vertex invariant : Program 5)
    (positive : Bool) (ps : Parameters α) (x y code out other mapped : OTerm α) (ts : α → OTerm β) :
    (inputs edge vertex invariant positive ps x y code out other mapped).subst (fun a => emb (ts a)) =
      inputs edge vertex invariant positive (fun i => (ps i).subst ts)
        (x.subst ts) (y.subst ts) (code.subst ts) (out.subst ts) (other.subst ts) (mapped.subst ts) := by
  unfold inputs invariantAt mappedAt
  simp only [conjunctionSubst,vertexAtSubst,checkerSubst,programSubst,consTermSubst,
    InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]

theorem rowSubst {α β : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) (ts : α → OTerm β) :
    (row edge vertex invariant ps code).subst (fun a => emb (ts a)) =
      row edge vertex invariant (fun i => (ps i).subst ts) (code.subst ts) := by
  unfold row matrix
  rw [allBlockSubst,liftedEmbedding,InternalAdditionLawsProof.impSubst,inputsSubst]
  unfold pathGraph
  rw [checkerSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr,
    InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]

theorem rowRename {α β : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) (j : α → β) :
    (row edge vertex invariant ps code).relabel j =
      row edge vertex invariant (fun i => (ps i).relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row edge vertex invariant ps code).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {α : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code x y out other mapped : OTerm α) :
    (matrix edge vertex invariant ps code).subst
      (Sum.elim Term.var (fun i => emb (![x,y,out,other,mapped] i))) =
      (inputs edge vertex invariant false ps x y code out other mapped).imp (pathGraph edge out other mapped) := by
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

theorem rowAtCode {α : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (code : OTerm α) :
    InternalListInduction.atCode
      (row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr 0))) code =
        row edge vertex invariant ps code := by
  rw [InternalListInduction.atCode,instantiate,bindEmbedding,rowSubst]
  simp only [liftBind,varBind]

theorem rowAtIndex {α : Type} (edge : Program 3) (vertex invariant : Program 5)
    (ps : Parameters α) (index : Fin 3) :
    InternalListInduction.atIndex
      (row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr 0))) index =
        row edge vertex invariant (fun i => (ps i).relabel Sum.inl) (.var (.inr index)) := by
  rw [InternalListInduction.atIndex,rowRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftSyntaxProof
