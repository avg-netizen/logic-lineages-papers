module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableTailProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion (drop)
open InternalRawListRecursionSyntaxProof InternalRawListRecursionSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open RankMemoDefinitions RankMemoCoherenceSyntax RankMemoTableTailProof
open InternalListCodec SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalListCodecSupportProof InternalPositiveUnfoldingSupportProof
open InternalClosedProgramsBindingProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open InternalTermSubstitutionProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (gap code small large : OTerm α)
    (hr : Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow gap)))
    (hs : Nonempty (Derivation body Gamma (graph1 table small code)))
    (hl : Nonempty (Derivation body Gamma (graph1 table large (add code gap)))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (RankMemoCoherenceSyntax.dropBody gap)
    (fun i => emb (![code,small,large] i)) hr
  rw [RankMemoCoherenceSyntax.dropBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hs⟩ := hs
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hs hl)⟩

theorem zeroCore (code small large : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 table small code)))
    (hl : Nonempty (Derivation body Gamma (graph1 table large (add code z)))) :
    Nonempty (Derivation body Gamma (dropGraph small z large)) := by
  have hl' := headTransport table large (add code z) code Fin.elim0 ⟨addZero code⟩ hl
  have he := valueUnique table large small (Fin.cons code Fin.elim0) hl' hs
  exact outputTransport drop large small (Fin.cons z (Fin.cons large Fin.elim0)) he (dropZero large)

theorem zeroRow : Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow z)) := by
  unfold RankMemoCoherenceSyntax.dropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let A := graph1 table s c ⊓ graph1 table l (add c z)
  obtain ⟨d⟩ := zeroCore (body := body) (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl))
    c s l
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [RankMemoCoherenceSyntax.dropBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Generalizing the older index lets the successor step use the preceding
row at code+1. No semantic lookup or recursion equation is reflected. -/
theorem successorCore (gap code small large : OTerm α)
    (hr : Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow gap)))
    (hs : Nonempty (Derivation body Gamma (graph1 table small code)))
    (hl : Nonempty (Derivation body Gamma (graph1 table large (add code (suc gap))))) :
    Nonempty (Derivation body Gamma (dropGraph small (suc gap) large)) := by
  apply programCases table (Fin.cons (suc code) Fin.elim0) _
  intro β j Delta next hj hn
  simp only [dropRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [RankMemoCoherenceSyntax.dropRowRename] at hr'
  have hs' := renameInto hs j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [graph1Rename,addRelabel,sucRelabel] at hs' hl'
  simp only [consTermRename,emptyRename,sucRelabel] at hn
  let c := code.relabel j
  let g := gap.relabel j
  have he : Nonempty (Derivation body Delta (eqn (add c (suc g)) (add (suc c) g))) :=
    ⟨trans (addSucc c g) (symm (leftSuccessor c g))⟩
  have hl'' := headTransport table (large.relabel j)
    (add c (suc g)) (add (suc c) g) Fin.elim0 he hl'
  have hd := rowApply g (suc c) next (large.relabel j) hr' hn hl''
  have ht := tableTail (small.relabel j) next c hs' hn
  exact dropNext (small.relabel j) next g (large.relabel j) hd ht

theorem successorRow (gap : OTerm α)
    (hr : Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow gap))) :
    Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow (suc gap))) := by
  unfold RankMemoCoherenceSyntax.dropRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let s : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let l : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let g := gap.relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := graph1 table s c ⊓ graph1 table l (add c (suc g))
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hr' := renameInto hr Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [RankMemoCoherenceSyntax.dropRowRename] at hr'
  obtain ⟨d⟩ := successorCore g c s l hr'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [RankMemoCoherenceSyntax.dropBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (gap : OTerm α) :
    Nonempty (Derivation body Gamma (RankMemoCoherenceSyntax.dropRow gap)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := RankMemoCoherenceSyntax.dropRow v
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,instantiate,bindEmbedding,RankMemoCoherenceSyntax.dropRowSubst,v,varBind]
    exact Classical.choice (zeroRow)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,successorInstance,nextEmbedding,RankMemoCoherenceSyntax.dropRowSubst,v,varNext]
    exact Classical.choice (successorRow v
      (show Nonempty (Derivation body (theta :: Gamma.map weaken) theta) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩))
  have d := Derivation.universalElimination (emb gap) (natInduction theta hb hs)
  simpa only [theta,instantiate,bindEmbedding,RankMemoCoherenceSyntax.dropRowSubst,v,varBind] using (Nonempty.intro d)

theorem tableDrop (gap code small large : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 table small code)))
    (hl : Nonempty (Derivation body Gamma (graph1 table large (add code gap)))) :
    Nonempty (Derivation body Gamma (dropGraph small gap large)) :=
  rowApply gap code small large (allRows gap) hs hl

/-- Retrieve the original recursor result at any earlier code, using an
object-language difference witness rather than an external decoding fact. -/
theorem tableLookup (result code gap large : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 decoder result code)))
    (ht : Nonempty (Derivation body Gamma (graph1 table large (add code gap)))) :
    Nonempty (Derivation body Gamma (lookupGraph result gap large)) := by
  apply programCases table (Fin.cons code Fin.elim0) _
  intro β j Delta small hj hs
  rw [lookupRename]
  have hr' := renameInto hr j Delta hj
  rw [graph1Rename] at hr'
  have ht' := renameInto ht j Delta hj
  simp only [graph1Rename,addRelabel] at ht'
  simp only [consTermRename,emptyRename] at hs
  have hh := decoderHead (result.relabel j) (code.relabel j) small
    hr' hs
  have hd := tableDrop (gap.relabel j) (code.relabel j) small (large.relabel j)
    hs ht'
  exact lookupValue (result.relabel j) (gap.relabel j) (large.relabel j) small hd hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableProof
