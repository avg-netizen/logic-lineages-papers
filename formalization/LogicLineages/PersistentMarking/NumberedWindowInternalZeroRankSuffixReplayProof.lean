module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankSuffixReplayProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc refl)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceOpenIntroProof (exact_InstallOpenZeroRankOutput)
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
  (loopAt exact_OpenParameterizedLoopStep)
open NumberedWindowInternalZeroRankOpenPathBuildProof (OriginalZeroPrefix)

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

/-- Append already-held finite arithmetic suffix rows to an actual run on
the joined tape, provided its real cursor has reached that exact suffix.
The joined certificate, physical callback and all prefix reports remain
unchanged; every subsequent hop reuses its same original advance and
actual zero test in this one proof body. This does not yet derive the
required positioned prefix from the original append graph. -/
theorem replay (g : Program 1) (raw : Program 5) (L : Program 3)
    (ctx ty start joined leftFuel leftState suffix a b suffixFuel suffixState cursor current : OTerm α)
    (left : Nonempty (Derivation B Γ
      (loopAt (zeroOutput g (advance raw L)) leftState leftFuel ctx ty start joined)))
    (atJoin : Nonempty (Derivation B Γ (scratchGraph leftState suffix (suc a))))
    (middle : Nonempty (Derivation B Γ (eqn a b)))
    (rows : OriginalZeroPrefix B Γ g raw L ctx ty (suc b) suffix
      suffixFuel suffixState cursor current) :
    ∃ used state : OTerm α,
      Nonempty (Derivation B Γ
        (loopAt (zeroOutput g (advance raw L)) state used ctx ty start joined)) ∧
      Nonempty (Derivation B Γ (scratchGraph state cursor current)) := by
  induction rows with
  | init _ =>
      exact ⟨leftFuel,leftState,left,changeScratchCurrent leftState suffix a b middle atJoin⟩
  | @cons fuel prior cur src hop tail dst out _ cell original rank after ih =>
      obtain ⟨used,state,before,scratch⟩ := ih
      have actual := exact_InstallOpenZeroRankOutput g (advance raw L) ![ctx,ty,src,hop] dst original rank
      have extended := exact_OpenParameterizedLoopStep (zeroOutput g (advance raw L))
        out state used ctx ty start joined cur src hop tail (suc dst) before scratch cell actual after
      exact ⟨suc used,out,extended,after⟩

#print axioms replay
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankSuffixReplayProof
