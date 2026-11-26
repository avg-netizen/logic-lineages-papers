module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendSyntaxProof
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

def fields (left right joined parameter mappedLeft mappedRight out : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joined left right ⊓
    (graph1 OriginalTypedArgumentObservations.reverse mappedLeft left ⊓
      (graph1 OriginalTypedArgumentObservations.reverse mappedRight right ⊓
        graph2 InternalApplicationValidityStackAppend.append out mappedRight mappedLeft))

def rowBody (left : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (fields (left.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
      (graph1 OriginalTypedArgumentObservations.reverse (.var (.inr 5)) (.var (.inr 1)))

def row (left : OTerm alpha) : Formula alpha := allBlock (rowBody left)

theorem fieldsSubst {beta : Type} 
    (left right joined parameter mappedLeft mappedRight out : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields left right joined parameter mappedLeft mappedRight out).subst (fun a => emb (ts a)) =
      fields (left.subst ts) (right.subst ts) (joined.subst ts) (parameter.subst ts)
        (mappedLeft.subst ts) (mappedRight.subst ts) (out.subst ts) := by
  simp only [fields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

theorem fieldsRename {beta : Type} 
    (left right joined parameter mappedLeft mappedRight out : OTerm alpha) (j : alpha → beta) :
    (fields left right joined parameter mappedLeft mappedRight out).relabel j =
      fields (left.relabel j) (right.relabel j) (joined.relabel j) (parameter.relabel j)
        (mappedLeft.relabel j) (mappedRight.relabel j) (out.relabel j) := by
  simp only [fields,conjunctionRename,graph1Rename,graph2Rename]

theorem rowSubst {beta : Type} (left : OTerm alpha) (ts : alpha → OTerm beta) :
    (row left).subst (fun a => emb (ts a)) = row (left.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (left : OTerm alpha) (j : alpha → beta) :
    (row left).relabel j = row (left.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row left).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowWitness (left right joined parameter mappedLeft mappedRight out : OTerm alpha) :
    (rowBody left).subst
      (Sum.elim Term.var (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i))) =
      (fields left right joined parameter mappedLeft mappedRight out).imp
        (graph1 OriginalTypedArgumentObservations.reverse out joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i))) =
      (fun x => emb (Sum.elim Term.var ![right,joined,parameter,mappedLeft,mappedRight,out] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowAtCode (left : OTerm alpha) :
    atCode (row (.var (.inr (0 : Fin 1)))) left = row left := by
  simp only [atCode,instantiate,bindEmbedding,rowSubst,varBind]

theorem rowAtIndex (i : Fin 3) :
    atIndex (row (.var (.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1))) i =
      row (.var (.inr i) : OTerm (alpha ⊕ Fin 3)) := by
  rw [atIndex,rowRename]
  rfl

theorem rowApply (left right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row left)))
    (hf : Nonempty (Derivation body Delta (fields left right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined)) := by
  have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody left)
    (fun i => emb (![right,joined,parameter,mappedLeft,mappedRight,out] i)) hi
  rw [rowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendSyntaxProof
