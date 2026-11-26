module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTickProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraph (recursion)
open ID1Completion.InternalRecursionGraphSuccessorEliminationProof
  (actualOriginalRecursionSuccessorElimination)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply successorCases)
open ID1Completion.InternalControlGraphSupportProof
  (programRename projectionValue recursionZeroValue valueUnique headTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn bindEmbedding nextEmbedding liftBind varBind zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (iterateState step)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename)
open NumberedWindowInternalSparseRawTickShapeTickProof (tickShape)
open NumberedWindowInternalSparseRawRunShapeLogicProof (goodTransport goodCases)
open NumberedWindowInternalSparseRawRunShapeMotiveProof
  (loopMotive motiveRename motiveSubst motiveIntro motiveApply)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Fuel zero: the literal projection returns the original start, whose
shape is the explicit premise. -/
theorem zeroMotive (p other : Program 3) (start : OTerm α)
    (hs : Nonempty (Derivation body Γ (goodState start))) :
    Nonempty (Derivation body Γ (loopMotive p other z start)) := by
  apply motiveIntro p other z start
  intro β j Δ o hj ho
  rw [zRelabel] at ho
  have hz : Nonempty (Derivation body Δ
      (programGraph (iterateState p other) (start.relabel j) ![z,start.relabel j])) :=
    recursionZeroValue (.projection 0) (step p other) (start.relabel j) ![start.relabel j]
      (projectionValue 0 ![start.relabel j])
  have he := valueUnique (iterateState p other) (start.relabel j) o ![z,start.relabel j] hz ho
  have hs' := renameInto hs j Δ hj
  rw [goodRename] at hs'
  exact goodTransport (start.relabel j) o he hs'

/-- Successor fuel: actual recursor elimination exposes the predecessor
result as an eigenvariable; the induction hypothesis is used at that
eigenvariable, its two quantifiers are eliminated, and the one-tick
shape is applied to the literal step after peeling projection 1. This
step's derivation uses only the induction hypothesis; the start's shape
premise enters through the zero case and is NOT redundant at positive
fuel (a malformed start with a zero frame read is returned unchanged). -/
theorem nextMotive (p other : Program 3) (start fuel : OTerm α)
    (ih : Nonempty (Derivation body Γ (loopMotive p other fuel start))) :
    Nonempty (Derivation body Γ (loopMotive p other (suc fuel) start)) := by
  apply motiveIntro p other (suc fuel) start
  intro β j Δ o hj ho
  rw [sucRelabel] at ho
  let f := OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1))
  let g := OrdinaryArithmetic.graphFormula (step p other)
  have ho' : Nonempty (Derivation body Δ
      (recursion f g o (suc (fuel.relabel j)) ![start.relabel j])) := ho
  have ds := closedApply (actualOriginalRecursionSuccessorElimination body 1 β f g o
    (fuel.relabel j) ![start.relabel j]) ho'
  have ih' := renameInto ih j Δ hj
  rw [motiveRename] at ih'
  apply successorCases Δ f g o (fuel.relabel j) ![start.relabel j] (goodState o) ds
  intro γ l Θ prev hl hprev hstep
  rw [goodRename]
  have ih'' := renameInto ih' l Θ hl
  rw [motiveRename] at ih''
  rw [inputsRename] at hprev hstep
  let fuel' : OTerm γ := (fuel.relabel j).relabel l
  let start' : OTerm γ := (start.relabel j).relabel l
  have hprev' : Nonempty (Derivation body Θ
      (programGraph (iterateState p other) prev ![fuel',start'])) := hprev
  have gp := motiveApply p other fuel' start' prev ih'' hprev'
  let xs : Fin 3 → OTerm γ := ![fuel',prev,start']
  have hstep' : Nonempty (Derivation body Θ (programGraph (step p other) (o.relabel l) xs)) :=
    hstep
  have tick : Nonempty (Derivation body Θ
      (programGraph (chosenTick p other) (o.relabel l) ![prev])) := by
    apply compositionRecover (chosenTick p other) (fun _ : Fin 1 => .projection 1)
      (o.relabel l) xs ![prev] hstep'
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  apply goodCases Θ prev (goodState (o.relabel l)) gp
  intro δ m Ξ a b hm he _
  rw [goodRename]
  have tick' := renameInto tick m Ξ hm
  rw [programRename,inputsRename] at tick'
  have moved : Nonempty (Derivation body Ξ
      (programGraph (chosenTick p other) ((o.relabel l).relabel m) ![stateTerm a b])) :=
    headTransport (chosenTick p other) ((o.relabel l).relabel m) (prev.relabel m)
      (stateTerm a b) ![] he tick'
  exact tickShape p other a b _ moved

/-- Object induction on fuel with the output universally bound inside the
motive and the original start fixed as an unchanged parameter. -/
theorem deriveMotive (p other : Program 3) (start fuel : OTerm α)
    (hs : Nonempty (Derivation body Γ (goodState start))) :
    Nonempty (Derivation body Γ (loopMotive p other fuel start)) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := loopMotive p other v (start.relabel j)
  have inst (t : OTerm α) : instantiate theta (emb t) = loopMotive p other t start := by
    simp only [theta,instantiate,bindEmbedding,motiveSubst,j,v,liftBind,varBind]
  have next : successorInstance theta = loopMotive p other (suc v) (start.relabel j) := by
    simp only [theta,successorInstance,nextEmbedding,motiveSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := zeroMotive p other start hs
  obtain ⟨stepd⟩ := nextMotive (Γ := theta :: Γ.map weaken) p other (start.relabel j) v
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result := Derivation.universalElimination (emb fuel)
    (natInduction theta (by rw [inst]; exact base) (by rw [next]; exact stepd))
  rw [inst] at result
  exact ⟨result⟩

theorem loopShape (p other : Program 3) (fuel start out : OTerm α)
    (hs : Nonempty (Derivation body Γ (goodState start)))
    (hg : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) out ![fuel,start]))) :
    Nonempty (Derivation body Γ (goodState out)) :=
  motiveApply p other fuel start out (deriveMotive p other start fuel hs) hg

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeInductionProof
