module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenTargets
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanImplies invariant invariantCode invariantIndex)
open NumberedWindowInternalSparseDirectedSeenOpenConsProof (consScan)

attribute [local irreducible] programGraph

private theorem nilCase (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty v : OTerm α) :
    Nonempty (Derivation body Γ (scanImplies E z ctx ty v)) := by
  let A := scanGraph E z ctx ty v
  let Δ := A :: Γ
  let params : Fin 3 → OTerm α := ![ctx,ty,v]
  have accepted : Nonempty (Derivation body Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have impossible := nilRecover (constantZero 3) (scanStep E) (suc z) params accepted
  obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc z) z params impossible
    (zeroConstantValue params)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply eq))⟩

private theorem consCase (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty v : OTerm α) :
    Nonempty (Derivation body Γ (constructors (invariant E ctx ty v))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (invariant E ctx ty v))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := scanImplies E t (ctx.relabel j) (ty.relabel j) (v.relabel j)
  let A := scanGraph E n (ctx.relabel j) (ty.relabel j) (v.relabel j)
  let Δ := A :: R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (invariant E ctx ty v) 2).imp (atIndex (invariant E ctx ty v) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := consScan (body := body) (Γ := Δ) E n h t
    (ctx.relabel j) (ty.relabel j) (v.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (Derivation.implicationIntroduction out))⟩

theorem exact_OpenDirectedSeenWitness : ExactOpenDirectedSeenWitness := by
  intro E body α Γ code ctx ty v
  have base : Nonempty (Derivation body Γ (atCode (invariant E ctx ty v) z)) := by
    rw [invariantCode]
    exact nilCase E body α Γ ctx ty v
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := consCase E body α Γ ctx ty v
  have original : Nonempty (Derivation body Γ (premises (invariant E ctx ty v))) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have d := actualOriginalListInductionAtCode body α Γ (invariant E ctx ty v) code original
  rw [invariantCode] at d
  exact d

#print axioms exact_OpenDirectedSeenWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenChecks
