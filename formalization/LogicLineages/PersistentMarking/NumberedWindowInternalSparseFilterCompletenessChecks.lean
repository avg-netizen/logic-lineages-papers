module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedFilter (cell pass passTape passGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitCases)
open NumberedWindowInternalSparseFilterCompletenessSyntaxProof
open NumberedWindowInternalSparseFilterCompletenessStepProof (atCons)
open NumberedWindowInternalSparseFilterCompletenessTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atNil (E : Program 4) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (completeAt E z seen ctx ty k)) := by
  let A := memberGraph z k ⊓ scanGraph E seen ctx ty k
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have nilRun := nilRecover memberBase memberStep (suc z) (![k] : Fin 1 → OTerm α) ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨e⟩ := valueUnique memberBase (suc z) z (![k] : Fin 1 → OTerm α) nilRun (zeroConstantValue _)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply e))⟩

private theorem consRule (E : Program 4) (seen ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (motive E seen ctx ty k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (motive E seen ctx ty k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := cell n h t
  let R := completeAt E t (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (motive E seen ctx ty k) 2).imp (atIndex (motive E seen ctx ty k) 0))))
  simp only [motiveIndex]
  obtain ⟨r⟩ := atCons (body := body) (Γ := Δ) E n h t (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j) ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction r)⟩

theorem exact_ScannedMemberRetention : ExactScannedMemberRetention := by
  intro E body α Γ out n seen ctx ty k
  let A := passGraph E out n seen ctx ty ⊓ (memberGraph n k ⊓ scanGraph E seen ctx ty k)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have basis : Nonempty (Derivation body Δ (atCode (motive E seen ctx ty k) z)) := by
    rw [motiveAt]
    exact atNil E seen ctx ty k
  obtain ⟨base⟩ := basis
  obtain ⟨step⟩ := consRule (body := body) (Γ := Δ) E seen ctx ty k
  have every := actualOriginalListInductionAtCode body α Δ (motive E seen ctx ty k) n
    ⟨Derivation.conjunctionIntroduction base step⟩
  rw [motiveAt] at every
  obtain ⟨rule⟩ := every
  have hit := Derivation.implicationElimination rule (Derivation.conjunctionRight h)
  have member : Nonempty (Derivation body Δ (memberGraph out k)) := by
    apply hitCases E n seen ctx ty k _ ⟨hit⟩
    intro β j Θ actual keep run m
    rw [graphRename]
    have supplied := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ keep
    rw [passRename] at supplied
    have same := valueUnique (pass E) actual (out.relabel j)
      (passTape (n.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)) run supplied
    exact headTransport scratchMember (suc z) actual (out.relabel j) ![k.relabel j] same m
  obtain ⟨r⟩ := member
  exact ⟨Derivation.implicationIntroduction r⟩

#print axioms exact_ScannedMemberRetention
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
