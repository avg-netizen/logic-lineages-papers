module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TailProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TableProof
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

open SyntaxProof TailProof
theorem rowApply (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (memoDropRow B R gap params)))
    (hs : Nonempty (Derivation body Gamma (memoGraph B R small code params)))
    (hl : Nonempty (Derivation body Gamma (memoGraph B R large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (memoBody B R gap params)
    (fun i => emb (![code,small,large] i)) hr
  rw [memoBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := hs
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hs hl)⟩

theorem zeroCore (B : Program 2) (R : Program 4)
    (code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (memoGraph B R small code params)))
    (hl : Nonempty (Derivation body Gamma (memoGraph B R large (add code z) params))) :
    Nonempty (Derivation body Gamma (dropGraph small z large)) := by
  have hl' := headTransport (ExchangeRowMemo.table B R) large (add code z) code params ⟨addZero code⟩ hl
  have he := valueUnique (ExchangeRowMemo.table B R) large small (Fin.cons code params) hl' hs
  exact outputTransport drop large small (Fin.cons z (Fin.cons large Fin.elim0)) he (dropZero large)

theorem zeroRow (B : Program 2) (R : Program 4)
    (params : Fin 2 → OTerm α) : Nonempty (Derivation body Gamma (memoDropRow B R z params)) := by
  unfold memoDropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := memoGraph B R s c ps ⊓ memoGraph B R l (add c z) ps
  obtain ⟨d⟩ := zeroCore (body := body) (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl))
    B R c s l ps
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [memoBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Generalizing the older index lets the successor step use the preceding
row at code+1. No semantic lookup or recursion equation is reflected. -/
theorem successorCore (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (memoDropRow B R gap params)))
    (hs : Nonempty (Derivation body Gamma (memoGraph B R small code params)))
    (hl : Nonempty (Derivation body Gamma (memoGraph B R large (add code (suc gap)) params))) :
    Nonempty (Derivation body Gamma (dropGraph small (suc gap) large)) := by
  apply programCases (ExchangeRowMemo.table B R) (Fin.cons (suc code) params) _
  intro β j Delta next hj hn
  simp only [dropRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [memoDropRowRename] at hr'
  have hs' := renameInto hs j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [memoRename,addRelabel,sucRelabel] at hs' hl'
  simp only [consTermRename,sucRelabel] at hn
  let c := code.relabel j
  let g := gap.relabel j
  let ps := fun i => (params i).relabel j
  have he : Nonempty (Derivation body Delta (eqn (add c (suc g)) (add (suc c) g))) :=
    ⟨trans (addSucc c g) (symm (leftSuccessor c g))⟩
  have hl'' := headTransport (ExchangeRowMemo.table B R) (large.relabel j)
    (add c (suc g)) (add (suc c) g) ps he hl'
  have hd := rowApply B R g (suc c) next (large.relabel j) ps hr' hn hl''
  have ht := TailProof.tableTail B R (small.relabel j) next c ps hs' hn
  exact dropNext (small.relabel j) next g (large.relabel j) hd ht

theorem successorRow (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (memoDropRow B R gap params))) :
    Nonempty (Derivation body Gamma (memoDropRow B R (suc gap) params)) := by
  unfold memoDropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let g := gap.relabel (Sum.inl : α → α ⊕ Fin 3)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := memoGraph B R s c ps ⊓ memoGraph B R l (add c (suc g)) ps
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hr' := renameInto hr Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [memoDropRowRename] at hr'
  obtain ⟨d⟩ := successorCore B R g c s l ps hr'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [memoBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) :
    Nonempty (Derivation body Gamma (memoDropRow B R gap params)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ps := fun i => (params i).relabel (Sum.inl : α → α ⊕ Fin 1)
  let theta := memoDropRow B R v ps
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,instantiate,bindEmbedding,memoDropRowSubst,v,ps,varBind,liftBind]
    exact Classical.choice (zeroRow B R params)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,memoDropRowSubst,v,ps,varNext,liftNext]
    exact Classical.choice (successorRow B R v ps
      (show Nonempty (Derivation body (theta :: Gamma.map weaken) theta) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have d := Derivation.universalElimination (emb gap) (natInduction theta hb hs)
  simpa only [theta,instantiate,bindEmbedding,memoDropRowSubst,v,ps,varBind,liftBind] using (Nonempty.intro d)

theorem tableDrop (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (memoGraph B R small code params)))
    (hl : Nonempty (Derivation body Gamma (memoGraph B R large (add code gap) params))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) :=
  rowApply B R gap code small large params (allRows B R gap params) hs hl

/-- Retrieve the original recursor result at any earlier code, using an
object-language difference witness rather than an external decoding fact. -/
theorem tableLookup (B : Program 2) (R : Program 4)
    (result code gap large : OTerm α) (params : Fin 2 → OTerm α)
    (hr : Nonempty (Derivation body Gamma (memoRowGraph B R result code params)))
    (ht : Nonempty (Derivation body Gamma (memoGraph B R large (add code gap) params))) :
    Nonempty (Derivation body Gamma (lookupGraph result gap large)) := by
  apply programCases (ExchangeRowMemo.table B R) (Fin.cons code params) _
  intro β j Delta small hj hs
  rw [lookupRename]
  have hr' := renameInto hr j Delta hj
  rw [memoRowRename] at hr'
  have ht' := renameInto ht j Delta hj
  simp only [memoRename,addRelabel] at ht'
  simp only [consTermRename] at hs
  have hh := memoHead B R (result.relabel j) (code.relabel j) small
    (fun i => (params i).relabel j) hr' hs
  have hd := tableDrop B R (gap.relabel j) (code.relabel j) small (large.relabel j)
    (fun i => (params i).relabel j) hs ht'
  exact lookupValue (result.relabel j) (gap.relabel j) (large.relabel j) small hd hh


theorem internalTableDrop : Targets.InternalTableDrop := by
  intro B R body alpha Delta index gap window bound small large hs hl
  exact tableDrop B R gap index small large ![window,bound] hs hl

theorem internalRowLookup : Targets.InternalRowLookup := by
  intro B R body alpha Delta index gap window bound value large hr ht
  exact tableLookup B R value index gap large ![window,bound] hr ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TableProof
