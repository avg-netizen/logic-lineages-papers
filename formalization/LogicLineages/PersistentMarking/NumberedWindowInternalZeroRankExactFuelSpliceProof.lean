module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankExactFuelSpliceProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc refl symm addZero addSucc)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceOpenIntroProof (exact_InstallOpenZeroRankOutput)
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
  (loopAt exact_OpenParameterizedLoopStep exact_OpenParameterizedLoopFuelTransport)
open NumberedWindowInternalZeroRankOpenPathBuildProof (OriginalZeroPrefix)
open NumberedWindowInternalParameterizedPositiveFoldOpenPaddingProof
  (exact_OpenParameterizedLoopPadding)
open NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof
  (exact_OpenParameterizedPositiveFromTerminal)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem changeScratchCurrent (state cursor a b : OTerm α)
    (same : Nonempty (Derivation B Γ (eqn a b)))
    (held : Nonempty (Derivation B Γ (scratchGraph state cursor (suc a)))) :
    Nonempty (Derivation B Γ (scratchGraph state cursor (suc b))) := by
  obtain ⟨h⟩ := same
  unfold scratchGraph programGraph at held ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula consCode)
    state ![cursor,suc a] ![cursor,suc b] _ held
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · change Nonempty (Derivation B Γ (equal cursor cursor))
    rw [equalEqn]
    exact ⟨refl cursor⟩
  · obtain rfl : k = 0 := Fin.eq_zero k
    change Nonempty (Derivation B Γ (equal (suc a) (suc b)))
    rw [equalEqn]
    exact ⟨congSuc h⟩

/-- Replay actual original zero rows with precise combined fuel,
not a new padded value; the held middle equation changes only the actual
scratch current, and every hop continues to use its original selectors. -/
theorem replay (g : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty start joined leftFuel leftState suffix a b suffixFuel suffixState cursor current : OTerm α)
    (left : Nonempty (Derivation B Γ
      (loopAt (zeroOutput g (advance raw L)) leftState leftFuel ctx ty start joined)))
    (atJoin : Nonempty (Derivation B Γ (scratchGraph leftState suffix (suc a))))
    (middle : Nonempty (Derivation B Γ (eqn a b)))
    (rows : OriginalZeroPrefix B Γ g raw L ctx ty (suc b) suffix
      suffixFuel suffixState cursor current) :
    ∃ state : OTerm α,
      Nonempty (Derivation B Γ
        (loopAt (zeroOutput g (advance raw L)) state (add leftFuel suffixFuel) ctx ty start joined)) ∧
      Nonempty (Derivation B Γ (scratchGraph state cursor current)) := by
  let A := zeroOutput g (advance raw L)
  induction rows with
  | init _ =>
      have padded := exact_OpenParameterizedLoopFuelTransport A leftState leftFuel (add leftFuel z)
        ctx ty start joined ⟨symm (addZero leftFuel)⟩ left
      exact ⟨leftState,padded,changeScratchCurrent leftState suffix a b middle atJoin⟩
  | @cons fuel prior cur src hop tail dst out _ cell original rank after ih =>
      obtain ⟨state,before,scratch⟩ := ih
      have actual := exact_InstallOpenZeroRankOutput g (advance raw L) ![ctx,ty,src,hop] dst original rank
      have extended := exact_OpenParameterizedLoopStep A out state (add leftFuel fuel)
        ctx ty start joined cur src hop tail (suc dst) before scratch cell actual after
      have finished := exact_OpenParameterizedLoopFuelTransport A out (suc (add leftFuel fuel))
        (add leftFuel (suc fuel)) ctx ty start joined ⟨symm (addSucc leftFuel fuel)⟩ extended
      exact ⟨out,finished,after⟩

/-- The actual original combined fuel gap and nonempty joined certificate
close the exact zero-positive graph. This is a finite-row splice after a
genuinely positioned left prefix, not an assertion of an arbitrary
symbolic append or a transfer from the ordinary positive checker. -/
theorem positive (g : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty source joined leftFuel leftState suffix a b suffixFuel suffixState target extra : OTerm α)
    (left : Nonempty (Derivation B Γ
      (loopAt (zeroOutput g (advance raw L)) leftState leftFuel ctx ty (suc source) joined)))
    (atJoin : Nonempty (Derivation B Γ (scratchGraph leftState suffix (suc a))))
    (middle : Nonempty (Derivation B Γ (eqn a b)))
    (rows : OriginalZeroPrefix B Γ g raw L ctx ty (suc b) suffix
      suffixFuel suffixState z (suc target))
    (gap : Nonempty (Derivation B Γ (eqn (add (add leftFuel suffixFuel) extra) joined)))
    (nonemptyCert : Nonempty (Derivation B Γ (eqn joined z).not)) :
    Nonempty (Derivation B Γ
      (programGraph (zeroPositive g raw L) (suc z) (args5 ctx ty source joined target))) := by
  let A := zeroOutput g (advance raw L)
  obtain ⟨state,run,done⟩ := replay g raw L ctx ty (suc source) joined leftFuel leftState suffix a b
    suffixFuel suffixState z (suc target) left atJoin middle rows
  have padded := exact_OpenParameterizedLoopPadding A state (add leftFuel suffixFuel) extra
    ctx ty (suc source) joined (suc target) run done
  have actual := exact_OpenParameterizedLoopFuelTransport A state
    (add (add leftFuel suffixFuel) extra) joined ctx ty (suc source) joined gap padded
  exact exact_OpenParameterizedPositiveFromTerminal A state ctx ty source joined target actual done nonemptyCert

#print axioms replay
#print axioms positive
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankExactFuelSpliceProof
