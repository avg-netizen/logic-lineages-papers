module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFinishTransferProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim zeroBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue projectionValue valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalListCodec (headCode tailCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankStepTransportProof (Report zeroTail vectorOneRename)
open NumberedWindowInternalZeroRankPairedStepProof (liveAgrees)
open NumberedWindowInternalZeroRankPairedLoopSyntaxProof (loop)
open NumberedWindowInternalZeroRankPairedLoopProof (applyRows exact_OpenZeroRankPairedLoop)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fourRename {β : Type} (c ty start raw : OTerm α) (j : α → β) :
    (fun i : Fin 4 => (![c,ty,start,raw] i).relabel j) =
      ![c.relabel j,ty.relabel j,start.relabel j,raw.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

private theorem stateToLoop (A : Program 4) (out c ty start cert : OTerm α)
    (h : Report (B := B) (Γ := Γ) (stateAt A) out ![c,ty,start,cert]) :
    Nonempty (Derivation B Γ (loop A out cert c ty start cert)) := by
  let xs := ![c,ty,start,cert]
  apply compositionRecover (iterateAt A)
    ![.projection 3,.projection 0,.projection 1,.projection 2,.projection 3]
    out xs ![cert,c,ty,start,cert] h
  intro i
  exact Fin.cases (projectionValue (3 : Fin 4) xs)
    (Fin.cases (projectionValue (0 : Fin 4) xs) (Fin.cases (projectionValue (1 : Fin 4) xs)
      (Fin.cases (projectionValue (2 : Fin 4) xs)
        (Fin.cases (projectionValue (3 : Fin 4) xs) (fun q => Fin.elim0 q))))) i

private def atState (A : Program 4) (p : Program 1) : Program 4 :=
  .composition p (fun _ : Fin 1 => stateAt A)

private theorem coordIntro (A : Program 4) (p : Program 1)
    (xs : Fin 4 → OTerm α) (out s : OTerm α)
    (state : Report (B := B) (Γ := Γ) (stateAt A) s xs)
    (val : Report (B := B) (Γ := Γ) p out ![s]) :
    Report (B := B) (Γ := Γ) (atState A p) out xs := by
  apply compositionValue p (fun _ : Fin 1 => stateAt A) out xs ![s] val
  intro i
  obtain rfl := Fin.eq_zero i
  exact state

private theorem coordElim (A : Program 4) (p : Program 1)
    (xs : Fin 4 → OTerm α) (out s : OTerm α)
    (state : Report (B := B) (Γ := Γ) (stateAt A) s xs)
    (val : Report (B := B) (Γ := Γ) (atState A p) out xs) :
    Report (B := B) (Γ := Γ) p out ![s] := by
  apply compositionRecover p (fun _ : Fin 1 => stateAt A) out xs ![s] val
  intro i
  obtain rfl := Fin.eq_zero i
  exact state

private theorem isLive (s value : OTerm α)
    (tail : Report (B := B) (Γ := Γ) tailCode (suc value) ![s]) :
    Nonempty (Derivation B Γ (zeroTail s).not) := by
  obtain ⟨orig⟩ := tail
  let Δ := zeroTail s :: Γ
  have fact : Derivation B Δ (zeroTail s) := Derivation.hypothesis List.mem_cons_self
  have localTail : Derivation B Δ (programGraph tailCode (suc value) ![s]) :=
    Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) orig
  obtain ⟨e⟩ := valueUnique tailCode (suc value) z ![s] ⟨localTail⟩ ⟨fact⟩
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply e)⟩

private theorem sameLiveState (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty start cert f u value : OTerm α)
    (a : Report (B := B) (Γ := Γ) (stateAt (zeroOutput g (advance raw least))) f ![c,ty,start,cert])
    (b : Report (B := B) (Γ := Γ) (stateAt (advance raw least)) u ![c,ty,start,cert])
    (tail : Report (B := B) (Γ := Γ) tailCode (suc value) ![f]) :
    Report (B := B) (Γ := Γ) (stateAt (advance raw least)) f ![c,ty,start,cert] := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  obtain ⟨r⟩ := applyRows A U cert c ty start cert f u
    (exact_OpenZeroRankPairedLoop g raw least cert c ty start cert)
    (stateToLoop A f c ty start cert a) (stateToLoop U u c ty start cert b)
  obtain ⟨live⟩ := isLive f value tail
  have e : Derivation B Γ (eqn f u) := Derivation.implicationElimination r live
  exact outputTransport (stateAt U) u f ![c,ty,start,cert] ⟨symm e⟩ b

private theorem transferKnown (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty start cert f u value : OTerm α)
    (a : Report (B := B) (Γ := Γ) (stateAt (zeroOutput g (advance raw least))) f ![c,ty,start,cert])
    (b : Report (B := B) (Γ := Γ) (stateAt (advance raw least)) u ![c,ty,start,cert])
    (held : Report (B := B) (Γ := Γ) (finishAt (zeroOutput g (advance raw least)))
      (suc value) ![c,ty,start,cert]) :
    Report (B := B) (Γ := Γ) (finishAt (advance raw least)) (suc value) ![c,ty,start,cert] := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  apply optionGraphCases headCode ![f] _
  · intro β j Δ keep h
    simp only [programRename,sucRelabel,fourRename]
    let xs := ![c.relabel j,ty.relabel j,start.relabel j,cert.relabel j]
    have before := renameInto a j Δ keep
    simp only [programRename,fourRename] at before
    have after := renameInto b j Δ keep
    simp only [programRename,fourRename] at after
    have accepted := renameInto held j Δ keep
    simp only [programRename,sucRelabel,fourRename] at accepted
    rw [vectorOneRename] at h
    have cur := coordIntro A headCode xs z (f.relabel j) before h
    have combined := zeroBranchElim (atState A headCode) (atState A tailCode) (constantZero 4)
      (suc (value.relabel j)) xs cur accepted
    have tail := coordElim A tailCode xs (suc (value.relabel j)) (f.relabel j) before combined
    have agreed := sameLiveState g raw least (c.relabel j) (ty.relabel j)
      (start.relabel j) (cert.relabel j) (f.relabel j) (u.relabel j) (value.relabel j) before after tail
    exact zeroBranchIntro (atState U headCode) (atState U tailCode) (constantZero 4)
      (suc (value.relabel j)) xs (coordIntro U headCode xs z (f.relabel j) agreed h)
      (coordIntro U tailCode xs (suc (value.relabel j)) (f.relabel j) agreed tail)
  · intro β j Δ k keep h
    let xs := ![c.relabel j,ty.relabel j,start.relabel j,cert.relabel j]
    have before := renameInto a j Δ keep
    simp only [programRename,fourRename] at before
    have accepted := renameInto held j Δ keep
    simp only [programRename,sucRelabel,fourRename] at accepted
    rw [vectorOneRename] at h
    have nonempty := coordIntro A headCode xs (suc k) (f.relabel j) before h
    have no := successorBranchElim (atState A headCode) (atState A tailCode) (constantZero 4)
      (suc (value.relabel j)) k xs nonempty accepted
    obtain ⟨e⟩ := valueUnique (constantZero 4) (suc (value.relabel j)) z xs no (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

/-- A live finish is transferred at exactly the raw-certificate-selected
fuel and unchanged raw cursor. Zero output alone does not transport. -/
theorem exact_OpenZeroRankFinishTransfer (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty start cert value : OTerm α)
    (held : Report (B := B) (Γ := Γ) (finishAt (zeroOutput g (advance raw least)))
      (suc value) ![c,ty,start,cert]) :
    Report (B := B) (Γ := Γ) (finishAt (advance raw least)) (suc value) ![c,ty,start,cert] := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  apply programCases (stateAt A) ![c,ty,start,cert] _
  intro β j Δ f keep h
  simp only [programRename,sucRelabel,fourRename]
  rw [fourRename] at h
  have ok := renameInto held j Δ keep
  simp only [programRename,sucRelabel,fourRename] at ok
  apply programCases (stateAt U) ![c.relabel j,ty.relabel j,start.relabel j,cert.relabel j] _
  intro γ k Ω u keep' p
  simp only [programRename,sucRelabel,fourRename]
  rw [fourRename] at p
  have carry := renameInto h k Ω keep'
  simp only [programRename,fourRename] at carry
  have proof := renameInto ok k Ω keep'
  simp only [programRename,sucRelabel,fourRename] at proof
  exact transferKnown g raw least ((c.relabel j).relabel k) ((ty.relabel j).relabel k)
    ((start.relabel j).relabel k) ((cert.relabel j).relabel k) (f.relabel k) u
    ((value.relabel j).relabel k) carry p proof

#print axioms exact_OpenZeroRankFinishTransfer
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFinishTransferProof
