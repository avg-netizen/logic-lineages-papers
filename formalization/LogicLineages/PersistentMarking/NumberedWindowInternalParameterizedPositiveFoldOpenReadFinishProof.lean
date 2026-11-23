module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputStateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationStatementChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadFinishProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (projectionValue compositionValue programRename outputTransport valueUnique headTransport zeroSuccessorCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (headCode tailCode)
open ID1Completion.InternalListCodecSupportProof (unaryGraph unaryGraphRename)
open ID1Completion.InternalListCodecDecompositionSupportProof (reconstructNonzero)
open ID1Completion.InternalListCodecEvaluationProof (tailEvaluation)
open ID1Completion.InternalNumeralEvaluationStatementChecks (numeral_evaluation_exact)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof (loopAt)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem literalUnaryZero (p : Program 1)
    (evaluated : evaluate p (List.Vector.cons 0 List.Vector.nil) = 0) :
    Nonempty (Derivation B Γ (unaryGraph p (z : OTerm α) z)) := by
  obtain ⟨d⟩ := numeral_evaluation_exact B 1 p
    (List.Vector.cons 0 List.Vector.nil) α
  rw [evaluated] at d
  have inputEq : (fun i : Fin 1 =>
      (SourceComputabilityFormulaSupportProof.numeral
        ((List.Vector.cons 0 List.Vector.nil).get i) : OTerm α)) =
      (Fin.cons z Fin.elim0 : Fin 1 → OTerm α) := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [inputEq] at d
  unfold unaryGraph programGraph
  exact ⟨weakenClosed d Γ⟩

private theorem zeroTail :
    Nonempty (Derivation B Γ (unaryGraph tailCode (z : OTerm α) z)) :=
  literalUnaryZero tailCode ((tailEvaluation 0).trans (by decide))

private theorem nonzeroOfTail (state target : OTerm α)
    (tail : Nonempty (Derivation B Γ (unaryGraph tailCode (suc target) state))) :
    Nonempty (Derivation B Γ (eqn state z).not) := by
  obtain ⟨tail⟩ := tail
  let Δ := eqn state z :: Γ
  have transported : Nonempty (Derivation B Δ (unaryGraph tailCode (suc target) z)) :=
    headTransport tailCode (suc target) state z Fin.elim0
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp tail _⟩
  obtain ⟨bad⟩ := valueUnique tailCode (suc target) z (Fin.cons z Fin.elim0) transported zeroTail
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private def atState (p : Program 1) (A : Program 4) : Program 4 :=
  .composition p (fun _ : Fin 1 => stateAt A)

private theorem lookup (p : Program 1) (A : Program 4) (out state : OTerm α)
    (xs : Fin 4 → OTerm α)
    (chosen : Nonempty (Derivation B Γ (programGraph (stateAt A) state xs)))
    (value : Nonempty (Derivation B Γ (unaryGraph p out state))) :
    Nonempty (Derivation B Γ (programGraph (atState p A) out xs)) :=
  compositionValue p (fun _ : Fin 1 => stateAt A) out xs (Fin.cons state Fin.elim0)
    value (fun i => by obtain rfl := Fin.eq_zero i; exact chosen)

private theorem recoverTail (A : Program 4) (state target : OTerm α)
    (xs : Fin 4 → OTerm α)
    (chosen : Nonempty (Derivation B Γ (programGraph (stateAt A) state xs)))
    (h : Nonempty (Derivation B Γ (programGraph (atState tailCode A) (suc target) xs))) :
    Nonempty (Derivation B Γ (unaryGraph tailCode (suc target) state)) :=
  compositionRecover tailCode (fun _ : Fin 1 => stateAt A) (suc target) xs
    (Fin.cons state Fin.elim0) h (fun i => by obtain rfl := Fin.eq_zero i; exact chosen)

private theorem readKnownState (A : Program 4) (state target : OTerm α)
    (xs : Fin 4 → OTerm α)
    (chosen : Nonempty (Derivation B Γ (programGraph (stateAt A) state xs)))
    (done : Nonempty (Derivation B Γ (programGraph (finishAt A) (suc target) xs))) :
    Nonempty (Derivation B Γ (scratchGraph state z (suc target))) := by
  apply programCases headCode (Fin.cons state Fin.elim0) _
  intro β j Δ head keep h
  rw [scratchRename,zRelabel,sucRelabel]
  have oneInput : (fun i : Fin 1 => (((Fin.cons state Fin.elim0 : Fin 1 → OTerm α) i).relabel j)) =
      Fin.cons (state.relabel j) Fin.elim0 := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [oneInput] at h
  have chosen' := renameInto chosen j Δ keep
  have done' := renameInto done j Δ keep
  rw [programRename] at chosen'
  rw [programRename,sucRelabel] at done'
  let xs' : Fin 4 → OTerm β := fun i => (xs i).relabel j
  apply zeroSuccessorCases Δ head _
  · obtain ⟨h⟩ := h
    obtain ⟨chosen'⟩ := chosen'
    obtain ⟨done'⟩ := done'
    let Δ' := eqn head z :: Δ
    have headZero : Nonempty (Derivation B Δ' (unaryGraph headCode z (state.relabel j))) :=
      outputTransport headCode head z (Fin.cons (state.relabel j) Fin.elim0)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp h _⟩
    have state' : Nonempty (Derivation B Δ' (programGraph (stateAt A) (state.relabel j) xs')) :=
      ⟨addHyp chosen' _⟩
    have tailAt := zeroBranchElim (atState headCode A) (atState tailCode A) (constantZero 4)
      (suc (target.relabel j)) xs' (lookup headCode A z (state.relabel j) xs' state' headZero)
      ⟨addHyp done' _⟩
    have tail := recoverTail A (state.relabel j) (target.relabel j) xs' state' tailAt
    exact reconstructNonzero (state.relabel j) z (suc (target.relabel j))
      (nonzeroOfTail (state.relabel j) (target.relabel j) tail) headZero tail
  · intro γ k Θ d keep' same
    rw [scratchRename,zRelabel,sucRelabel]
    have head' := renameInto h k Θ keep'
    have chosen'' := renameInto chosen' k Θ keep'
    have done'' := renameInto done' k Θ keep'
    rw [unaryGraphRename] at head'
    rw [programRename] at chosen''
    rw [programRename,sucRelabel] at done''
    let xs'' : Fin 4 → OTerm γ := fun i => ((xs i).relabel j).relabel k
    let t := (state.relabel j).relabel k
    let out := suc ((target.relabel j).relabel k)
    have headPos : Nonempty (Derivation B Θ (unaryGraph headCode (suc d) t)) :=
      outputTransport headCode (head.relabel k) (suc d) (Fin.cons t Fin.elim0) same head'
    have impossible := successorBranchElim (atState headCode A) (atState tailCode A)
      (constantZero 4) out d xs'' (lookup headCode A (suc d) t xs'' chosen'' headPos) done''
    obtain ⟨bad⟩ := valueUnique (constantZero 4) out z xs'' impossible (zeroConstantValue xs'')
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

private theorem stateLoop (A : Program 4) (state c ty start cert : OTerm α)
    (chosen : Nonempty (Derivation B Γ (programGraph (stateAt A) state (args4 c ty start cert)))) :
    Nonempty (Derivation B Γ (loopAt A state cert c ty start cert)) := by
  let xs := args4 c ty start cert
  apply compositionRecover (iterateAt A) NumberedWindowInternalSparsePositiveOutputStateProof.picks
    state xs ![cert,c,ty,start,cert] chosen
  intro i
  exact Fin.cases (projectionValue (3 : Fin 4) xs)
    (Fin.cases (projectionValue (0 : Fin 4) xs) (Fin.cases (projectionValue (1 : Fin 4) xs)
      (Fin.cases (projectionValue (2 : Fin 4) xs) (Fin.cases (projectionValue (3 : Fin 4) xs)
        (fun u => Fin.elim0 u))))) i

private theorem argsRename {β : Type} (j : α → β) (c ty start cert : OTerm α) :
    (fun i => (args4 c ty start cert i).relabel j) =
      args4 (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun u => Fin.elim0 u)))) i

/-- An actual successful finish reports the actual chosen state at the
original certificate fuel and its certified nil-cursor/successor-value
scratch. No state supplied by the caller or mirrored by host evaluation. -/
theorem exact_OpenParameterizedReadFinish (A : Program 4) (c ty start cert target : OTerm α)
    (goal : Formula α)
    (done : Nonempty (Derivation B Γ (programGraph (finishAt A) (suc target) (args4 c ty start cert))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (loopAt A state (cert.relabel j) (c.relabel j)
        (ty.relabel j) (start.relabel j) (cert.relabel j))) →
      Nonempty (Derivation B Δ (scratchGraph state z (suc (target.relabel j)))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases (stateAt A) (args4 c ty start cert) goal
  intro β j Δ state keep chosen
  have result := renameInto done j Δ keep
  rw [argsRename] at chosen
  rw [programRename,sucRelabel,argsRename] at result
  exact next β j Δ state keep
    (stateLoop A state (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j) chosen)
    (readKnownState A state (target.relabel j) _ chosen result)

#print axioms exact_OpenParameterizedReadFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadFinishProof
