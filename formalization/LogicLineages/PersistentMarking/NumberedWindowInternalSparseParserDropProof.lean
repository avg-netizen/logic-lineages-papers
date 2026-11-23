module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserDropSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserDropProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (drop)
open ID1Completion.InternalRawListRecursionSyntaxProof (dropGraph dropRename)
open ID1Completion.InternalRawListRecursionSupportProof (dropZero dropNext)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel bindEmbedding liftBind varBind nextEmbedding eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans natInduction addZero addSucc)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction actualFiniteUniversalElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalAdditionLawsProof (add leftSuccessor varNext liftNext)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel ltF)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseParserTableLocalProof (tableReport exact_OriginalSparseParserTableTail)
open NumberedWindowInternalSparseParserDropSyntaxProof
open NumberedWindowInternalSparseDecodeDifferenceProof (differenceEquation)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (scratchDropMotive B R gap params)))
    (hs : Nonempty (Derivation body Gamma (tableReport B R small code params)))
    (hl : Nonempty (Derivation body Gamma (tableReport B R large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (scratchDropBody B R gap params)
    (fun i => emb (![code,small,large] i)) hr
  rw [scratchDropBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := hs
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hs hl)⟩

theorem zeroCore (B : Program 2) (R : Program 4)
    (code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (tableReport B R small code params)))
    (hl : Nonempty (Derivation body Gamma (tableReport B R large (add code z) params))) :
    Nonempty (Derivation body Gamma (dropGraph small z large)) := by
  have hl' := headTransport (scratchTable B R) large (add code z) code params ⟨addZero code⟩ hl
  have he := valueUnique (scratchTable B R) large small (Fin.cons code params) hl' hs
  exact outputTransport drop large small (Fin.cons z (Fin.cons large Fin.elim0)) he (dropZero large)

theorem zeroRow (B : Program 2) (R : Program 4)
    (params : Fin 2 → OTerm α) : Nonempty (Derivation body Gamma (scratchDropMotive B R z params)) := by
  unfold scratchDropMotive
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := tableReport B R s c ps ⊓ tableReport B R l (add c z) ps
  obtain ⟨d⟩ := zeroCore (body := body) (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl))
    B R c s l ps
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [scratchDropBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Generalizing the older index lets the successor step use the preceding
row at code+1. No semantic lookup or recursion equation is reflected. -/
theorem successorCore (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (scratchDropMotive B R gap params)))
    (hs : Nonempty (Derivation body Gamma (tableReport B R small code params)))
    (hl : Nonempty (Derivation body Gamma (tableReport B R large (add code (suc gap)) params))) :
    Nonempty (Derivation body Gamma (dropGraph small (suc gap) large)) := by
  apply programCases (scratchTable B R) (Fin.cons (suc code) params) _
  intro β j Delta next hj hn
  simp only [dropRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [scratchDropMotiveRename] at hr'
  have hs' := renameInto hs j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [tableReportRename,addRelabel,sucRelabel] at hs' hl'
  simp only [consTermRename,sucRelabel] at hn
  let c := code.relabel j
  let g := gap.relabel j
  let ps := fun i => (params i).relabel j
  have he : Nonempty (Derivation body Delta (eqn (add c (suc g)) (add (suc c) g))) :=
    ⟨trans (addSucc c g) (symm (leftSuccessor c g))⟩
  have hl'' := headTransport (scratchTable B R) (large.relabel j)
    (add c (suc g)) (add (suc c) g) ps he hl'
  have hd := rowApply B R g (suc c) next (large.relabel j) ps hr' hn hl''
  have ht := exact_OriginalSparseParserTableTail B R (small.relabel j) next c ps hs' hn
  exact dropNext (small.relabel j) next g (large.relabel j) hd ht

theorem successorRow (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (scratchDropMotive B R gap params))) :
    Nonempty (Derivation body Gamma (scratchDropMotive B R (suc gap) params)) := by
  unfold scratchDropMotive
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let g := gap.relabel (Sum.inl : α → α ⊕ Fin 3)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := tableReport B R s c ps ⊓ tableReport B R l (add c (suc g)) ps
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hr' := renameInto hr Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [scratchDropMotiveRename] at hr'
  obtain ⟨d⟩ := successorCore B R g c s l ps hr'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [scratchDropBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) :
    Nonempty (Derivation body Gamma (scratchDropMotive B R gap params)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 1)
  let theta := scratchDropMotive B R v ps
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,instantiate,bindEmbedding,scratchDropMotiveSubst,v,ps,varBind,liftBind]
    exact Classical.choice (zeroRow B R params)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,scratchDropMotiveSubst,v,ps,varNext,liftNext]
    exact Classical.choice (successorRow B R v ps
      (show Nonempty (Derivation body (theta :: Gamma.map weaken) theta) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have d := Derivation.universalElimination (emb gap) (natInduction theta hb hs)
  simpa only [theta,instantiate,bindEmbedding,scratchDropMotiveSubst,v,ps,varBind,liftBind] using (Nonempty.intro d)

theorem exact_OriginalSparseParserTableDrop (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (tableReport B R small code params)))
    (hl : Nonempty (Derivation body Gamma (tableReport B R large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) :=
  rowApply B R gap code small large params (allRows B R gap params) hs hl

/-- Convert an *actual*, properly oriented subtraction proof into the
index gap, under the internal nontruncation bound. The drop result is still
on the exact two supplied original table reports. -/
theorem exact_OriginalSparseParserTableDropAtDifference (B : Program 2) (R : Program 4)
    (lo hi gap small large : OTerm α) (params : Fin 2 → OTerm α)
    (bound : Nonempty (Derivation body Gamma (ltF lo (suc hi))))
    (difference : Nonempty (Derivation body Gamma (subGraph gap lo hi)))
    (low : Nonempty (Derivation body Gamma (tableReport B R small lo params)))
    (high : Nonempty (Derivation body Gamma (tableReport B R large hi params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) := by
  obtain ⟨indexEq⟩ := differenceEquation lo hi gap bound difference
  have moved : Nonempty (Derivation body Gamma (tableReport B R large (add lo gap) params)) :=
    headTransport (scratchTable B R) large hi (add lo gap) params ⟨symm indexEq⟩ high
  exact exact_OriginalSparseParserTableDrop B R gap lo small large params low moved

#print axioms exact_OriginalSparseParserTableDrop
#print axioms exact_OriginalSparseParserTableDropAtDifference

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserDropProof
