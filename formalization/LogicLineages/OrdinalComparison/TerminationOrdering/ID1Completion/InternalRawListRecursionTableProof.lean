module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalRawListRecursionSupportProof
open InternalListCodec SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalListCodecSupportProof InternalPositiveUnfoldingSupportProof
open InternalClosedProgramsBindingProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalTermSubstitutionProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply {k : Nat} (base : Program k) (step : Program (k + 2))
    (gap code small large : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (dropRow base step gap params)))
    (hs : Nonempty (Derivation body Gamma (tableGraph base step small code params)))
    (hl : Nonempty (Derivation body Gamma (tableGraph base step large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (dropBody base step gap params)
    (fun i => emb (![code,small,large] i)) hr
  rw [dropBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := hs
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hs hl)⟩

theorem zeroCore {k : Nat} (base : Program k) (step : Program (k + 2))
    (code small large : OTerm α) (params : Fin k → OTerm α)
    (hs : Nonempty (Derivation body Gamma (tableGraph base step small code params)))
    (hl : Nonempty (Derivation body Gamma (tableGraph base step large (add code z) params))) :
    Nonempty (Derivation body Gamma (dropGraph small z large)) := by
  have hl' := headTransport (table base step) large (add code z) code params ⟨addZero code⟩ hl
  have he := valueUnique (table base step) large small (Fin.cons code params) hl' hs
  exact outputTransport drop large small (Fin.cons z (Fin.cons large Fin.elim0)) he (dropZero large)

theorem zeroRow {k : Nat} (base : Program k) (step : Program (k + 2))
    (params : Fin k → OTerm α) : Nonempty (Derivation body Gamma (dropRow base step z params)) := by
  unfold dropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := tableGraph base step s c ps ⊓ tableGraph base step l (add c z) ps
  obtain ⟨d⟩ := zeroCore (body := body) (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl))
    base step c s l ps
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [dropBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Generalizing the older index lets the successor step use the preceding
row at code+1. No semantic lookup or recursion equation is reflected. -/
theorem successorCore {k : Nat} (base : Program k) (step : Program (k + 2))
    (gap code small large : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (dropRow base step gap params)))
    (hs : Nonempty (Derivation body Gamma (tableGraph base step small code params)))
    (hl : Nonempty (Derivation body Gamma (tableGraph base step large (add code (suc gap)) params))) :
    Nonempty (Derivation body Gamma (dropGraph small (suc gap) large)) := by
  apply programCases (table base step) (Fin.cons (suc code) params) _
  intro β j Delta next hj hn
  simp only [dropRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [dropRowRename] at hr'
  have hs' := renameInto hs j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [tableRename,addRelabel,sucRelabel] at hs' hl'
  simp only [consTermRename,sucRelabel] at hn
  let c := code.relabel j
  let g := gap.relabel j
  let ps := fun i => (params i).relabel j
  have he : Nonempty (Derivation body Delta (eqn (add c (suc g)) (add (suc c) g))) :=
    ⟨trans (addSucc c g) (symm (leftSuccessor c g))⟩
  have hl'' := headTransport (table base step) (large.relabel j)
    (add c (suc g)) (add (suc c) g) ps he hl'
  have hd := rowApply base step g (suc c) next (large.relabel j) ps hr' hn hl''
  have ht := tableTail base step (small.relabel j) next c ps hs' hn
  exact dropNext (small.relabel j) next g (large.relabel j) hd ht

theorem successorRow {k : Nat} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (dropRow base step gap params))) :
    Nonempty (Derivation body Gamma (dropRow base step (suc gap) params)) := by
  unfold dropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let g := gap.relabel (Sum.inl : α → α ⊕ Fin 3)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := tableGraph base step s c ps ⊓ tableGraph base step l (add c (suc g)) ps
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hr' := renameInto hr Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [dropRowRename] at hr'
  obtain ⟨d⟩ := successorCore base step g c s l ps hr'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [dropBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows {k : Nat} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α) :
    Nonempty (Derivation body Gamma (dropRow base step gap params)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 1)
  let theta := dropRow base step v ps
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,instantiate,bindEmbedding,dropRowSubst,v,ps,varBind,liftBind]
    exact Classical.choice (zeroRow base step params)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,dropRowSubst,v,ps,varNext,liftNext]
    exact Classical.choice (successorRow base step v ps
      (show Nonempty (Derivation body (theta :: Gamma.map weaken) theta) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have d := Derivation.universalElimination (emb gap) (natInduction theta hb hs)
  simpa only [theta,instantiate,bindEmbedding,dropRowSubst,v,ps,varBind,liftBind] using (Nonempty.intro d)

theorem tableDrop {k : Nat} (base : Program k) (step : Program (k + 2))
    (gap code small large : OTerm α) (params : Fin k → OTerm α)
    (hs : Nonempty (Derivation body Gamma (tableGraph base step small code params)))
    (hl : Nonempty (Derivation body Gamma (tableGraph base step large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) :=
  rowApply base step gap code small large params (allRows base step gap params) hs hl

/-- Retrieve the original recursor result at any earlier code, using an
object-language difference witness rather than an external decoding fact. -/
theorem tableLookup {k : Nat} (base : Program k) (step : Program (k + 2))
    (result code gap large : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (recGraph base step result code params)))
    (ht : Nonempty (Derivation body Gamma (tableGraph base step large (add code gap) params))) :
    Nonempty (Derivation body Gamma (lookupGraph result gap large)) := by
  apply programCases (table base step) (Fin.cons code params) _
  intro β j Delta small hj hs
  rw [lookupRename]
  have hr' := renameInto hr j Delta hj
  rw [recRename] at hr'
  have ht' := renameInto ht j Delta hj
  simp only [tableRename,addRelabel] at ht'
  simp only [consTermRename] at hs
  have hh := recHead base step (result.relabel j) (code.relabel j) small
    (fun i => (params i).relabel j) hr' hs
  have hd := tableDrop base step (gap.relabel j) (code.relabel j) small (large.relabel j)
    (fun i => (params i).relabel j) hs ht'
  exact lookupValue (result.relabel j) (gap.relabel j) (large.relabel j) small hd hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTableProof
