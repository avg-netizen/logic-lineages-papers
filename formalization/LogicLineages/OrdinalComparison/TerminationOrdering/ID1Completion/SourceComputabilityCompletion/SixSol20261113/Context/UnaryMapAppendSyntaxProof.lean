module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm row
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalListInduction InternalListInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map
  InternalApplicationValidityStackAppend.append

def fields (F : Program 1) (left right joined parameter mappedLeft mappedRight out : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joined left right ⊓
    (graph1 (InternalListMap.map (k := 0) F) mappedLeft left ⊓
      (graph1 (InternalListMap.map (k := 0) F) mappedRight right ⊓
        graph2 InternalApplicationValidityStackAppend.append out mappedLeft mappedRight))

def rowBody (F : Program 1) (left : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (fields F (left.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
      (graph1 (InternalListMap.map (k := 0) F) (.var (.inr 5)) (.var (.inr 1)))

def row (F : Program 1) (left : OTerm alpha) : Formula alpha := allBlock (rowBody F left)

theorem fieldsSubst {beta : Type} (F : Program 1)
    (left right joined parameter mappedLeft mappedRight out : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields F left right joined parameter mappedLeft mappedRight out).subst (fun a => emb (ts a)) =
      fields F (left.subst ts) (right.subst ts) (joined.subst ts) (parameter.subst ts)
        (mappedLeft.subst ts) (mappedRight.subst ts) (out.subst ts) := by
  simp only [fields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

theorem fieldsRename {beta : Type} (F : Program 1)
    (left right joined parameter mappedLeft mappedRight out : OTerm alpha) (j : alpha → beta) :
    (fields F left right joined parameter mappedLeft mappedRight out).relabel j =
      fields F (left.relabel j) (right.relabel j) (joined.relabel j) (parameter.relabel j)
        (mappedLeft.relabel j) (mappedRight.relabel j) (out.relabel j) := by
  simp only [fields,conjunctionRename,graph1Rename,graph2Rename]

theorem rowSubst {beta : Type} (F : Program 1) (left : OTerm alpha) (ts : alpha → OTerm beta) :
    (row F left).subst (fun a => emb (ts a)) = row F (left.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (F : Program 1) (left : OTerm alpha) (j : alpha → beta) :
    (row F left).relabel j = row F (left.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row F left).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowWitness (F : Program 1) (left right joined parameter mappedLeft mappedRight out : OTerm alpha) :
    (rowBody F left).subst
      (Sum.elim Term.var (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i))) =
      (fields F left right joined parameter mappedLeft mappedRight out).imp
        (graph1 (InternalListMap.map (k := 0) F) out joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i))) =
      (fun x => emb (Sum.elim Term.var ![right,joined,parameter,mappedLeft,mappedRight,out] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowAtCode (F : Program 1) (left : OTerm alpha) :
    atCode (row F (.var (.inr (0 : Fin 1)))) left = row F left := by
  simp only [atCode,instantiate,bindEmbedding,rowSubst,varBind]

theorem rowAtIndex (F : Program 1) (i : Fin 3) :
    atIndex (row F (.var (.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1))) i =
      row F (.var (.inr i) : OTerm (alpha ⊕ Fin 3)) := by
  rw [atIndex,rowRename]
  rfl

theorem rowApply (F : Program 1) (left right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row F left)))
    (hf : Nonempty (Derivation body Delta (fields F left right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined)) := by
  have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody F left)
    (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i)) hi
  rw [rowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendSyntaxProof
