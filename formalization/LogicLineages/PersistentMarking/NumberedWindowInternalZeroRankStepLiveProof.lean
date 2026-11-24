module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepDeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepLiveProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchElim zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport emptyRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode tailCode)
open ID1Completion.InternalRawListRecursionSupportProof (consTail)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePositiveFold (scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankStepTransportProof
open NumberedWindowInternalZeroRankStepDeadProof (goodUpdate badOutput)
open NumberedWindowInternalZeroRankAdvanceOpenProof (exact_OpenFilteredAdvanceLive)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem notRename {α β : Type} (f : Formula α) (j : α → β) :
    f.not.relabel j = (f.relabel j).not := rfl

private theorem liveTail (s h t : OTerm α)
    (alive : Nonempty (Derivation B Γ (zeroTail s).not))
    (packed : Report (B := B) (Γ := Γ) consCode s ![h,t]) :
    Nonempty (Derivation B Γ (eqn t z).not) := by
  obtain ⟨alive⟩ := alive
  obtain ⟨read⟩ := consTail s h t packed
  let Δ := eqn t z :: Γ
  have same : Derivation B Δ (eqn t z) := Derivation.hypothesis List.mem_cons_self
  have tailZero : Nonempty (Derivation B Δ (zeroTail s)) :=
    outputTransport tailCode t z ![s] ⟨same⟩ ⟨Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) read⟩
  obtain ⟨tailZero⟩ := tailZero
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) alive) tailZero)⟩

private theorem ordinaryAdvanceAt (g : Program 1) (raw : Program 5) (least : Program 3)
    (xs : Fin 6 → OTerm α) (out current hop : OTerm α)
    (checkedCurrent : Report (B := B) (Γ := Γ) scratchCurrent current xs)
    (checkedHop : Report (B := B) (Γ := Γ) (onCursor cellHead) hop xs)
    (filtered : Report (B := B) (Γ := Γ) (advanceAt (zeroOutput g (advance raw least))) out xs)
    (live : Nonempty (Derivation B Γ (eqn out z).not)) :
    Report (B := B) (Γ := Γ) (advanceAt (advance raw least)) out xs := by
  have original : Report (B := B) (Γ := Γ) (zeroOutput g (advance raw least)) out
      ![xs 2,xs 3,current,hop] := by
    apply compositionRecover (zeroOutput g (advance raw least))
      ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
      out xs ![xs 2,xs 3,current,hop] filtered
    intro i
    exact Fin.cases (projectionValue (2 : Fin 6) xs)
      (Fin.cases (projectionValue (3 : Fin 6) xs) (Fin.cases checkedCurrent
        (Fin.cases checkedHop (fun j => Fin.elim0 j)))) i
  exact advanceIntro (advance raw least) xs out current hop checkedCurrent checkedHop
    (exact_OpenFilteredAdvanceLive g (advance raw least) out ![xs 2,xs 3,current,hop] original live)

private theorem ordinaryUpdate (g : Program 1) (raw : Program 5) (least : Program 3)
    (xs : Fin 6 → OTerm α) (out : OTerm α)
    (alive : Nonempty (Derivation B Γ (zeroTail out).not))
    (held : Report (B := B) (Γ := Γ) (updateAt (zeroOutput g (advance raw least))) out xs) :
    Report (B := B) (Γ := Γ) (updateAt (advance raw least)) out xs := by
  let A := zeroOutput g (advance raw least)
  apply programCompositionCases consCode ![onCursor cellTail,advanceAt A] out xs _ held
  intro β j parts Δ keep packed components
  rw [programRename]
  let ys := fun i => (xs i).relabel j
  have h := renameInto alive j Δ keep
  simp only [notRename,zeroTailRename] at h
  have pack : Report (B := B) (Γ := Δ) consCode (out.relabel j) ![parts 0,parts 1] := by
    rw [vectorTwoEta]
    exact packed
  have hw := liveTail (out.relabel j) (parts 0) (parts 1) h pack
  apply programCases scratchCurrent ys _
  intro γ k Ω current keep' atCur
  rw [programRename]
  let zs := fun i => (ys i).relabel k
  have hp := renameInto pack k Ω keep'
  simp only [programRename,vectorTwoRename] at hp
  have ht := renameInto (components 0) k Ω keep'
  rw [programRename] at ht
  have hn := renameInto (components 1) k Ω keep'
  rw [programRename] at hn
  have useful := renameInto hw k Ω keep'
  simp only [notRename,ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,zRelabel] at useful
  apply programCases (onCursor cellHead) zs _
  intro δ l Θ hop keep'' atHop
  rw [programRename]
  let vs := fun i => (zs i).relabel l
  have cp := renameInto hp l Θ keep''
  simp only [programRename,vectorTwoRename] at cp
  have ct := renameInto ht l Θ keep''
  rw [programRename] at ct
  have cn := renameInto hn l Θ keep''
  rw [programRename] at cn
  have cc := renameInto atCur l Θ keep''
  rw [programRename] at cc
  have cl := renameInto useful l Θ keep''
  simp only [notRename,ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,zRelabel] at cl
  have result := ordinaryAdvanceAt g raw least vs (((parts 1).relabel k).relabel l)
    (current.relabel l) hop cc atHop cn cl
  exact updateIntro (advance raw least) vs (((out.relabel j).relabel k).relabel l)
    (((parts 0).relabel k).relabel l) (((parts 1).relabel k).relabel l) ct result cp

/-- A filtered step with a live final current validates the same output
for the ordinary step at the very same input scratch and parameters. -/
theorem exact_OpenFilteredStepWhenLive (g : Program 1) (raw : Program 5) (least : Program 3)
    (xs : Fin 6 → OTerm α) (out : OTerm α)
    (alive : Nonempty (Derivation B Γ (zeroTail out).not))
    (held : Report (B := B) (Γ := Γ) (stepAt (zeroOutput g (advance raw least))) out xs) :
    Report (B := B) (Γ := Γ) (stepAt (advance raw least)) out xs := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  apply optionGraphCases scratchCursor xs _
  · intro β j Δ keep nil
    rw [programRename]
    have h := renameInto held j Δ keep
    rw [programRename] at h
    have p := zeroBranchElim scratchCursor (.projection 1)
      (branch (onCursor cellGood) dead (updateAt A)) (out.relabel j) _ nil h
    exact zeroBranchIntro scratchCursor (.projection 1)
      (branch (onCursor cellGood) dead (updateAt U)) (out.relabel j) _ nil p
  · intro β j Δ cur keep live
    let ys := fun i => (xs i).relabel j
    rw [programRename]
    have h := renameInto held j Δ keep
    rw [programRename] at h
    have still := renameInto alive j Δ keep
    simp only [notRename,zeroTailRename] at still
    apply optionGraphCases (onCursor cellGood) ys _
    · intro γ k Ω keep' bad
      rw [programRename]
      let zs := fun i => (ys i).relabel k
      let o := (out.relabel j).relabel k
      have moved := renameInto h k Ω keep'
      rw [programRename] at moved
      have ok := renameInto live k Ω keep'
      simp only [programRename,sucRelabel] at ok
      have d := badOutput A zs (cur.relabel k) o ok bad moved
      have i := zeroBranchIntro (onCursor cellGood) dead (updateAt U) o zs bad d
      exact successorBranchIntro scratchCursor (.projection 1)
        (branch (onCursor cellGood) dead (updateAt U)) o (cur.relabel k) zs ok i
    · intro γ k Ω mark keep' good
      rw [programRename]
      let zs := fun i => (ys i).relabel k
      let o := (out.relabel j).relabel k
      have moved := renameInto h k Ω keep'
      rw [programRename] at moved
      have ok := renameInto live k Ω keep'
      simp only [programRename,sucRelabel] at ok
      have on := renameInto still k Ω keep'
      simp only [notRename,zeroTailRename] at on
      have v := ordinaryUpdate g raw least zs o on
        (goodUpdate A zs (cur.relabel k) mark o ok good moved)
      exact goodStep U zs (cur.relabel k) mark o ok good v

#print axioms exact_OpenFilteredStepWhenLive
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankStepLiveProof
