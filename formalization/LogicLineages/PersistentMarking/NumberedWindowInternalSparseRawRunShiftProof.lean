module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraph (recursion)
open ID1Completion.InternalRecursionGraphSuccessorEliminationProof
  (actualOriginalRecursionSuccessorElimination)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
  (recursionSuccessorIntroduction)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply successorCases)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue projectionValue recursionZeroValue valueUnique outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn bindEmbedding nextEmbedding liftBind varBind zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename)
open NumberedWindowInternalSparseRawRunShiftMotiveProof
  (shiftMotive shiftMotiveRename shiftMotiveSubst shiftMotiveIntro shiftMotiveApply)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The literal recursor step graph from a supplied tick at its previous
value. The step ignores its prior-fuel and original-input slots. -/
theorem stepFromTick (p other : Program 3) (out prev fuel start : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) out ![prev]))) :
    Nonempty (Derivation body Γ (programGraph (step p other) out ![fuel,prev,start])) := by
  let xs : Fin 3 → OTerm α := ![fuel,prev,start]
  apply compositionValue (chosenTick p other) (fun _ : Fin 1 => .projection 1) out xs ![prev] ht
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 xs

/-- One genuine recursor successor from a supplied prior run and tick. -/
theorem runSuccessor (p other : Program 3) (out prev fuel start : OTerm α)
    (prior : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) prev ![fuel,start])))
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) out ![prev]))) :
    Nonempty (Derivation body Γ (programGraph (iterateState p other) out ![suc fuel,start])) :=
  recursionSuccessorIntroduction (n := 1) Γ
    (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula (step p other)) out fuel prev ![start] prior
    (stepFromTick p other out prev fuel start ht)

theorem zeroShift (p other : Program 3) (start next : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) next ![start]))) :
    Nonempty (Derivation body Γ (shiftMotive p other z start next)) := by
  apply shiftMotiveIntro p other z start next
  intro β j Δ o hj ho
  rw [zRelabel] at ho ⊢
  have ht' := renameInto ht j Δ hj
  rw [programRename,inputsRename] at ht'
  have atNext : Nonempty (Derivation body Δ
      (programGraph (iterateState p other) (next.relabel j) ![z,next.relabel j])) :=
    recursionZeroValue (.projection 0) (step p other) (next.relabel j) ![next.relabel j]
      (projectionValue 0 ![next.relabel j])
  have he := valueUnique (iterateState p other) (next.relabel j) o ![z,next.relabel j] atNext ho
  have atStart : Nonempty (Derivation body Δ
      (programGraph (iterateState p other) (start.relabel j) ![z,start.relabel j])) :=
    recursionZeroValue (.projection 0) (step p other) (start.relabel j) ![start.relabel j]
      (projectionValue 0 ![start.relabel j])
  have one := runSuccessor p other (next.relabel j) (start.relabel j) z (start.relabel j)
    atStart ht'
  exact outputTransport (iterateState p other) (next.relabel j) o
    ![suc z,start.relabel j] he one

/-- The successor case never consults the supplied first tick: actual
recursor elimination exposes the predecessor run and the literal step,
whose tick is recovered and replayed one fuel later. -/
theorem nextShift (p other : Program 3) (fuel start next : OTerm α)
    (ih : Nonempty (Derivation body Γ (shiftMotive p other fuel start next))) :
    Nonempty (Derivation body Γ (shiftMotive p other (suc fuel) start next)) := by
  apply shiftMotiveIntro p other (suc fuel) start next
  intro β j Δ o hj ho
  rw [sucRelabel] at ho ⊢
  let f := OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1))
  let g := OrdinaryArithmetic.graphFormula (step p other)
  have ho' : Nonempty (Derivation body Δ
      (recursion f g o (suc (fuel.relabel j)) ![next.relabel j])) := ho
  have ds := closedApply (actualOriginalRecursionSuccessorElimination body 1 β f g o
    (fuel.relabel j) ![next.relabel j]) ho'
  have ih' := renameInto ih j Δ hj
  rw [shiftMotiveRename] at ih'
  apply successorCases Δ f g o (fuel.relabel j) ![next.relabel j] _ ds
  intro γ l Θ prev hl hprev hstep
  rw [programRename,pairRename,sucRelabel,sucRelabel]
  have ih'' := renameInto ih' l Θ hl
  rw [shiftMotiveRename] at ih''
  rw [inputsRename] at hprev hstep
  let fuel' : OTerm γ := (fuel.relabel j).relabel l
  let start' : OTerm γ := (start.relabel j).relabel l
  let next' : OTerm γ := (next.relabel j).relabel l
  have hprev' : Nonempty (Derivation body Θ
      (programGraph (iterateState p other) prev ![fuel',next'])) := hprev
  have late := shiftMotiveApply p other fuel' start' next' prev ih'' hprev'
  let xs : Fin 3 → OTerm γ := ![fuel',prev,next']
  have hstep' : Nonempty (Derivation body Θ (programGraph (step p other) (o.relabel l) xs)) :=
    hstep
  have tick : Nonempty (Derivation body Θ
      (programGraph (chosenTick p other) (o.relabel l) ![prev])) := by
    apply compositionRecover (chosenTick p other) (fun _ : Fin 1 => .projection 1)
      (o.relabel l) xs ![prev] hstep'
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact runSuccessor p other (o.relabel l) prev (suc fuel') start' late tick

theorem deriveShift (p other : Program 3) (start next fuel : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) next ![start]))) :
    Nonempty (Derivation body Γ (shiftMotive p other fuel start next)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := shiftMotive p other v (start.relabel j) (next.relabel j)
  have inst (t : OTerm α) : instantiate theta (emb t) = shiftMotive p other t start next := by
    simp only [theta,instantiate,bindEmbedding,shiftMotiveSubst,j,v,liftBind,varBind]
  have next' : successorInstance theta =
      shiftMotive p other (suc v) (start.relabel j) (next.relabel j) := by
    simp only [theta,successorInstance,nextEmbedding,shiftMotiveSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := zeroShift p other start next ht
  obtain ⟨stepd⟩ := nextShift (Γ := theta :: Γ.map weaken) p other v (start.relabel j)
    (next.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result := Derivation.universalElimination (emb fuel)
    (natInduction theta (by rw [inst]; exact base) (by rw [next']; exact stepd))
  rw [inst] at result
  exact ⟨result⟩

/-- Early-to-late direction of the first-tick shift. -/
theorem shiftLate (p other : Program 3) (start next fuel out : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) next ![start])))
    (he : Nonempty (Derivation body Γ (programGraph (iterateState p other) out ![fuel,next]))) :
    Nonempty (Derivation body Γ (programGraph (iterateState p other) out ![suc fuel,start])) :=
  shiftMotiveApply p other fuel start next out (deriveShift p other start next fuel ht) he

/-- Late-to-early direction: original totality supplies the early value,
which the forward direction and functionality identify with the output. -/
theorem shiftEarly (p other : Program 3) (start next fuel out : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph (chosenTick p other) next ![start])))
    (hl : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) out ![suc fuel,start]))) :
    Nonempty (Derivation body Γ (programGraph (iterateState p other) out ![fuel,next])) := by
  apply programCases (iterateState p other) ![fuel,next] _
  intro β j Δ v hj hv
  rw [programRename,pairRename]
  rw [pairRename] at hv
  have ht' := renameInto ht j Δ hj
  rw [programRename,inputsRename] at ht'
  have hl' := renameInto hl j Δ hj
  rw [programRename,pairRename,sucRelabel] at hl'
  have late := shiftLate p other (start.relabel j) (next.relabel j) (fuel.relabel j) v ht' hv
  have he := valueUnique (iterateState p other) v (out.relabel j)
    ![suc (fuel.relabel j),start.relabel j] late hl'
  exact outputTransport (iterateState p other) v (out.relabel j)
    ![fuel.relabel j,next.relabel j] he hv

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftProof
