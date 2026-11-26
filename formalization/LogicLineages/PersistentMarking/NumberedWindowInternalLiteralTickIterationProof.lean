module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationProof
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
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename)
open NumberedWindowInternalLiteralTickIterationMotiveProof
  (tickLoop tickStep shiftMotive shiftMotiveRename shiftMotiveSubst shiftMotiveIntro shiftMotiveApply)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The literal recursor step graph from a supplied tick at its previous
value. The step ignores its prior-fuel and original-input slots. -/
theorem stepFromTick (tickProgram : Program 1) (out prev fuel start : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram out ![prev]))) :
    Nonempty (Derivation body Γ (programGraph (tickStep tickProgram) out ![fuel,prev,start])) := by
  let xs : Fin 3 → OTerm α := ![fuel,prev,start]
  apply compositionValue tickProgram (fun _ : Fin 1 => .projection 1) out xs ![prev] ht
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 xs

/-- One genuine recursor successor from a supplied prior run and tick. -/
theorem runSuccessor (tickProgram : Program 1) (out prev fuel start : OTerm α)
    (prior : Nonempty (Derivation body Γ
      (programGraph (tickLoop tickProgram) prev ![fuel,start])))
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram out ![prev]))) :
    Nonempty (Derivation body Γ (programGraph (tickLoop tickProgram) out ![suc fuel,start])) :=
  recursionSuccessorIntroduction (n := 1) Γ
    (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula (tickStep tickProgram)) out fuel prev ![start] prior
    (stepFromTick tickProgram out prev fuel start ht)

theorem zeroShift (tickProgram : Program 1) (start next : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram next ![start]))) :
    Nonempty (Derivation body Γ (shiftMotive tickProgram z start next)) := by
  apply shiftMotiveIntro tickProgram z start next
  intro β j Δ o hj ho
  rw [zRelabel] at ho ⊢
  have ht' := renameInto ht j Δ hj
  rw [programRename,inputsRename] at ht'
  have atNext : Nonempty (Derivation body Δ
      (programGraph (tickLoop tickProgram) (next.relabel j) ![z,next.relabel j])) :=
    recursionZeroValue (.projection 0) (tickStep tickProgram) (next.relabel j) ![next.relabel j]
      (projectionValue 0 ![next.relabel j])
  have he := valueUnique (tickLoop tickProgram) (next.relabel j) o ![z,next.relabel j] atNext ho
  have atStart : Nonempty (Derivation body Δ
      (programGraph (tickLoop tickProgram) (start.relabel j) ![z,start.relabel j])) :=
    recursionZeroValue (.projection 0) (tickStep tickProgram) (start.relabel j) ![start.relabel j]
      (projectionValue 0 ![start.relabel j])
  have one := runSuccessor tickProgram (next.relabel j) (start.relabel j) z (start.relabel j)
    atStart ht'
  exact outputTransport (tickLoop tickProgram) (next.relabel j) o
    ![suc z,start.relabel j] he one

/-- The successor case never consults the supplied first tick: actual
recursor elimination exposes the predecessor run and the literal step,
whose tick is recovered and replayed one fuel later. -/
theorem nextShift (tickProgram : Program 1) (fuel start next : OTerm α)
    (ih : Nonempty (Derivation body Γ (shiftMotive tickProgram fuel start next))) :
    Nonempty (Derivation body Γ (shiftMotive tickProgram (suc fuel) start next)) := by
  apply shiftMotiveIntro tickProgram (suc fuel) start next
  intro β j Δ o hj ho
  rw [sucRelabel] at ho ⊢
  let f := OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1))
  let g := OrdinaryArithmetic.graphFormula (tickStep tickProgram)
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
      (programGraph (tickLoop tickProgram) prev ![fuel',next'])) := hprev
  have late := shiftMotiveApply tickProgram fuel' start' next' prev ih'' hprev'
  let xs : Fin 3 → OTerm γ := ![fuel',prev,next']
  have hstep' : Nonempty (Derivation body Θ (programGraph (tickStep tickProgram) (o.relabel l) xs)) :=
    hstep
  have tick : Nonempty (Derivation body Θ
      (programGraph tickProgram (o.relabel l) ![prev])) := by
    apply compositionRecover tickProgram (fun _ : Fin 1 => .projection 1)
      (o.relabel l) xs ![prev] hstep'
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  exact runSuccessor tickProgram (o.relabel l) prev (suc fuel') start' late tick

theorem deriveShift (tickProgram : Program 1) (start next fuel : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram next ![start]))) :
    Nonempty (Derivation body Γ (shiftMotive tickProgram fuel start next)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := shiftMotive tickProgram v (start.relabel j) (next.relabel j)
  have inst (t : OTerm α) : instantiate theta (emb t) = shiftMotive tickProgram t start next := by
    simp only [theta,instantiate,bindEmbedding,shiftMotiveSubst,j,v,liftBind,varBind]
  have next' : successorInstance theta =
      shiftMotive tickProgram (suc v) (start.relabel j) (next.relabel j) := by
    simp only [theta,successorInstance,nextEmbedding,shiftMotiveSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := zeroShift tickProgram start next ht
  obtain ⟨stepd⟩ := nextShift (Γ := theta :: Γ.map weaken) tickProgram v (start.relabel j)
    (next.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result := Derivation.universalElimination (emb fuel)
    (natInduction theta (by rw [inst]; exact base) (by rw [next']; exact stepd))
  rw [inst] at result
  exact ⟨result⟩

/-- Early-to-late direction of the first-tick shift. -/
theorem shiftLate (tickProgram : Program 1) (start next fuel out : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram next ![start])))
    (he : Nonempty (Derivation body Γ (programGraph (tickLoop tickProgram) out ![fuel,next]))) :
    Nonempty (Derivation body Γ (programGraph (tickLoop tickProgram) out ![suc fuel,start])) :=
  shiftMotiveApply tickProgram fuel start next out (deriveShift tickProgram start next fuel ht) he

/-- Late-to-early direction: original totality supplies the early value,
which the forward direction and functionality identify with the output. -/
theorem shiftEarly (tickProgram : Program 1) (start next fuel out : OTerm α)
    (ht : Nonempty (Derivation body Γ (programGraph tickProgram next ![start])))
    (hl : Nonempty (Derivation body Γ
      (programGraph (tickLoop tickProgram) out ![suc fuel,start]))) :
    Nonempty (Derivation body Γ (programGraph (tickLoop tickProgram) out ![fuel,next])) := by
  apply programCases (tickLoop tickProgram) ![fuel,next] _
  intro β j Δ v hj hv
  rw [programRename,pairRename]
  rw [pairRename] at hv
  have ht' := renameInto ht j Δ hj
  rw [programRename,inputsRename] at ht'
  have hl' := renameInto hl j Δ hj
  rw [programRename,pairRename,sucRelabel] at hl'
  have late := shiftLate tickProgram (start.relabel j) (next.relabel j) (fuel.relabel j) v ht' hv
  have he := valueUnique (tickLoop tickProgram) v (out.relabel j)
    ![suc (fuel.relabel j),start.relabel j] late hl'
  exact outputTransport (tickLoop tickProgram) v (out.relabel j)
    ![fuel.relabel j,next.relabel j] he hv

#print axioms runSuccessor
#print axioms shiftLate
#print axioms shiftEarly
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationProof
