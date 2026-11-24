module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof
  (valueUnique recursionZeroValue outputTransport programRename)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn eqnRelabel emb z suc zRelabel sucRelabel bindEmbedding liftBind varBind nextEmbedding nextTerm nextLift)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm natInduction)
open ID1Completion.InternalClosedProgramsBindingProof
  (actualFiniteUniversalIntroduction actualFiniteUniversalElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (initial)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6 selectedRename callRename)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgsRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold (stepAt iterateAt)
open NumberedWindowInternalZeroRankStepTransportProof (Report zeroTail)
open NumberedWindowInternalZeroRankPairedStepProof
open NumberedWindowInternalZeroRankPairedLoopSyntaxProof


variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fourRename {α β : Type} (c ty start raw : OTerm α) (j : α → β) :
    (fun i : Fin 4 => (![c,ty,start,raw] i).relabel j) =
      ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem applyRows (A U : Program 4) (k c ty start raw out ord : OTerm α)
    (chart : Nonempty (Derivation B Γ (rows A U k c ty start raw)))
    (f : Nonempty (Derivation B Γ (loop A out k c ty start raw)))
    (u : Nonempty (Derivation B Γ (loop U ord k c ty start raw))) :
    Nonempty (Derivation B Γ (liveAgrees out ord)) := by
  have h := actualFiniteUniversalElimination B α 2 Γ (rowsBody A U k c ty start raw)
    (fun i => emb (![out,ord] i)) chart
  rw [rowsBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨f⟩ := f
  obtain ⟨u⟩ := u
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction f u)⟩

private theorem baseCore (A U : Program 4) (c ty start raw out ord : OTerm α)
    (f : Nonempty (Derivation B Γ (loop A out z c ty start raw)))
    (u : Nonempty (Derivation B Γ (loop U ord z c ty start raw))) :
    Nonempty (Derivation B Γ (eqn out ord)) := by
  apply programCases initial ![c,ty,start,raw] _
  intro β j Δ startValue keep report
  rw [eqnRelabel]
  have prev := renameInto f j Δ keep
  have plain := renameInto u j Δ keep
  simp only [loopRename,zRelabel] at prev plain
  have own : Report (B := B) (Γ := Δ) initial startValue
      ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] := by
    simpa only [fourRename] using report
  have a := recursionZeroValue initial (stepAt A) startValue
    ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] own
  have b := recursionZeroValue initial (stepAt U) startValue
    ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] own
  let ys := ![z,c.relabel j,ty.relabel j,start.relabel j,raw.relabel j]
  obtain ⟨e₁⟩ := valueUnique (iterateAt A) (out.relabel j) startValue ys prev a
  obtain ⟨e₂⟩ := valueUnique (iterateAt U) startValue (ord.relabel j) ys b plain
  exact ⟨trans e₁ e₂⟩

theorem baseRows (A U : Program 4) (c ty start raw : OTerm α) :
    Nonempty (Derivation B Γ (rows A U z c ty start raw)) := by
  unfold rows
  apply actualFiniteUniversalIntroduction B α 2 Γ
  let j : α → α ⊕ Fin 2 := Sum.inl
  let out : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let ord : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let H := loop A out z (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j) ⊓
    loop U ord z (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j)
  let Δ := H :: Γ.map (fun p => p.relabel j)
  have h : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := baseCore A U (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j)
    out ord ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  have result : Derivation B Δ (liveAgrees out ord) :=
    Derivation.implicationIntroduction (Derivation.weakening (fun _ h' => List.mem_cons_of_mem _ h') e)
  simpa only [rowsBody,matrix,zRelabel] using
    (Nonempty.intro (Derivation.implicationIntroduction result))

private theorem loopStep (A : Program 4) (k c ty start raw prior out : OTerm α)
    (old : Nonempty (Derivation B Γ (loop A prior k c ty start raw)))
    (held : Nonempty (Derivation B Γ (loop A out (suc k) c ty start raw))) :
    Report (B := B) (Γ := Γ) (stepAt A) out (call6 k prior c ty start raw) := by
  apply programCases (stepAt A) (call6 k prior c ty start raw) _
  intro β j Δ value keep proposed
  rw [selectedRename]
  rw [callRename] at proposed
  have old' := renameInto old j Δ keep
  rw [loopRename] at old'
  have held' := renameInto held j Δ keep
  simp only [loopRename,sucRelabel] at held'
  let p := ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j]
  have lifted : Nonempty (Derivation B Δ
      (loop A value (suc (k.relabel j)) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j))) :=
    recursionSuccessorIntroduction Δ (OrdinaryArithmetic.graphFormula initial)
      (OrdinaryArithmetic.graphFormula (stepAt A)) value (k.relabel j) (prior.relabel j) p old' proposed
  have eq := valueUnique (iterateAt A) value (out.relabel j)
    ![suc (k.relabel j),c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] lifted held'
  exact outputTransport (stepAt A) value (out.relabel j)
    (call6 (k.relabel j) (prior.relabel j) (c.relabel j)
      (ty.relabel j) (start.relabel j) (raw.relabel j)) eq proposed

private theorem succCore (g : Program 1) (rawRel : Program 5) (least : Program 3)
    (k c ty start raw out ord : OTerm α)
    (prev : Nonempty (Derivation B Γ
      (rows (zeroOutput g (advance rawRel least)) (advance rawRel least) k c ty start raw)))
    (f : Nonempty (Derivation B Γ (loop (zeroOutput g (advance rawRel least)) out (suc k) c ty start raw)))
    (u : Nonempty (Derivation B Γ (loop (advance rawRel least) ord (suc k) c ty start raw))) :
    Nonempty (Derivation B Γ (liveAgrees out ord)) := by
  let A := zeroOutput g (advance rawRel least)
  let U := advance rawRel least
  apply programCases (iterateAt A) ![k,c,ty,start,raw] _
  intro β j Δ oldF keep report
  rw [liveAgreesRename]
  have ofg : Nonempty (Derivation B Δ
      (loop A oldF (k.relabel j) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j))) := by
    simpa only [loop,loopArgsRename] using report
  have keepPrev := renameInto prev j Δ keep
  rw [rowsRename] at keepPrev
  have fn := renameInto f j Δ keep
  simp only [loopRename,sucRelabel] at fn
  have un := renameInto u j Δ keep
  simp only [loopRename,sucRelabel] at un
  apply programCases (iterateAt U) ![k.relabel j,c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] _
  intro γ l Ω oldU keep' report'
  rw [liveAgreesRename]
  have oug : Nonempty (Derivation B Ω
      (loop U oldU ((k.relabel j).relabel l) ((c.relabel j).relabel l) ((ty.relabel j).relabel l)
        ((start.relabel j).relabel l) ((raw.relabel j).relabel l))) := by
    simpa only [loop,loopArgsRename] using report'
  have of' := renameInto ofg l Ω keep'
  rw [loopRename] at of'
  have previous := renameInto keepPrev l Ω keep'
  rw [rowsRename] at previous
  have fn' := renameInto fn l Ω keep'
  simp only [loopRename,sucRelabel] at fn'
  have un' := renameInto un l Ω keep'
  simp only [loopRename,sucRelabel] at un'
  let k' := (k.relabel j).relabel l
  let c' := (c.relabel j).relabel l
  let t' := (ty.relabel j).relabel l
  let s' := (start.relabel j).relabel l
  let r' := (raw.relabel j).relabel l
  let f' := (out.relabel j).relabel l
  let u' := (ord.relabel j).relabel l
  have agrees := applyRows A U k' c' t' s' r' (oldF.relabel l) oldU previous of' oug
  exact exact_OpenZeroRankPairedStep g rawRel least k' (oldF.relabel l) oldU f' u' c' t' s' r'
    agrees (loopStep A k' c' t' s' r' (oldF.relabel l) f' of' fn')
    (loopStep U k' c' t' s' r' oldU u' oug un')

theorem succRows (g : Program 1) (rawRel : Program 5) (least : Program 3)
    (k c ty start raw : OTerm α)
    (prev : Nonempty (Derivation B Γ
      (rows (zeroOutput g (advance rawRel least)) (advance rawRel least) k c ty start raw))) :
    Nonempty (Derivation B Γ
      (rows (zeroOutput g (advance rawRel least)) (advance rawRel least) (suc k) c ty start raw)) := by
  unfold rows
  apply actualFiniteUniversalIntroduction B α 2 Γ
  let A := zeroOutput g (advance rawRel least)
  let U := advance rawRel least
  let j : α → α ⊕ Fin 2 := Sum.inl
  let out : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let ord : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let H := loop A out (suc (k.relabel j)) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j) ⊓
    loop U ord (suc (k.relabel j)) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j)
  let Δ := H :: Γ.map (fun p => p.relabel j)
  have h : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have moved := renameInto prev j Δ keep
  rw [rowsRename] at moved
  obtain ⟨result⟩ := succCore g rawRel least (k.relabel j) (c.relabel j) (ty.relabel j)
    (start.relabel j) (raw.relabel j) out ord moved
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  simpa only [rowsBody,matrix,sucRelabel] using
    (Nonempty.intro (Derivation.implicationIntroduction result))

attribute [local irreducible] programGraph rows

/-- Internal Nat induction over the same arbitrary fuel, holding the
original cursor and all four parameters fixed. -/
theorem exact_OpenZeroRankPairedLoop (g : Program 1) (rawRel : Program 5) (least : Program 3)
    (k c ty start raw : OTerm α) :
    Nonempty (Derivation B Γ
      (rows (zeroOutput g (advance rawRel least)) (advance rawRel least) k c ty start raw)) := by
  let A := zeroOutput g (advance rawRel least)
  let U := advance rawRel least
  let j : α → α ⊕ Fin 1 := Sum.inl
  let θ : Formula (α ⊕ Fin 1) :=
    rows A U (.var (.inr 0)) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j)
  have init : Nonempty (Derivation B Γ (instantiate θ (emb z))) := by
    dsimp only [θ,j]
    rw [instantiate,bindEmbedding,rowsSubst]
    simp only [j,liftBind,varBind]
    exact baseRows A U c ty start raw
  have step : Nonempty (Derivation B (θ :: Γ.map weaken) (successorInstance θ)) := by
    have held : Nonempty (Derivation B (θ :: Γ.map weaken) θ) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have more := succRows g rawRel least (.var (.inr 0)) (c.relabel j) (ty.relabel j)
      (start.relabel j) (raw.relabel j) held
    dsimp only [θ,j]
    rw [successorInstance,nextEmbedding,rowsSubst]
    simp only [j,nextLift,nextTerm,Term.subst,Sum.elim_inr]
    exact more
  obtain ⟨init⟩ := init
  obtain ⟨step⟩ := step
  have done := Derivation.universalElimination (emb k) (natInduction θ init step)
  dsimp only [θ,j] at done
  rw [instantiate,bindEmbedding,rowsSubst] at done
  simpa only [liftBind,varBind] using (Nonempty.intro done)

#print axioms exact_OpenZeroRankPairedLoop
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopProof
