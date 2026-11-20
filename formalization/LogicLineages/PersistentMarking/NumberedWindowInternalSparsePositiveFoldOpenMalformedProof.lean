module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenBaseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellFailureProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenMalformedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue zeroSuccessorCases equalEqn outputTransport)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood)
open NumberedWindowInternalSparseFieldCellFailureProof (openFailure)
open NumberedWindowInternalSparseFieldInductionTargets (malformed nonzero)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem deadGraph (out : OTerm α) (args : Fin 6 → OTerm α)
    (state : Nonempty (Derivation body Γ (scratchGraph out z z))) :
    Nonempty (Derivation body Γ (programGraph dead out args)) := by
  apply compositionValue consCode ![constantZero 6,constantZero 6] out args ![z,z] state
  intro i
  exact Fin.cases (zeroConstantValue args) (Fin.cases (zeroConstantValue args) (fun k => Fin.elim0 k)) i

private theorem takeNonzero (raw : Program 5) (p : Program 3)
    (out k prior c ty start cert cursor : OTerm α)
    (nz : Nonempty (Derivation body Γ (eqn cursor z).not))
    (known : Nonempty (Derivation body Γ (programGraph scratchCursor cursor (call6 k prior c ty start cert))))
    (inside : Nonempty (Derivation body Γ (programGraph (branch (onCursor cellGood) dead (updateCell raw p))
      out (call6 k prior c ty start cert)))) :
    Nonempty (Derivation body Γ (stepGraph raw p out k prior c ty start cert)) := by
  obtain ⟨nz⟩ := nz
  apply zeroSuccessorCases Γ cursor _
  · exact ⟨Derivation.explosion (Derivation.implicationElimination
      (addHyp nz _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro β j Δ pred hJ ⟨e⟩
    change Nonempty (Derivation body Δ
      ((programGraph (iterateStep raw p) out (call6 k prior c ty start cert)).relabel j))
    rw [selectedRename]
    let args := call6 (k.relabel j) (prior.relabel j) (c.relabel j)
      (ty.relabel j) (start.relabel j) (cert.relabel j)
    have chosen := moveSelected j Δ hJ scratchCursor cursor k prior c ty start cert known
    have next := moveSelected j Δ hJ (branch (onCursor cellGood) dead (updateCell raw p))
      out k prior c ty start cert inside
    exact successorBranchIntro scratchCursor (.projection 1)
      (branch (onCursor cellGood) dead (updateCell raw p)) (out.relabel j) pred args
      (outputTransport scratchCursor (cursor.relabel j) (suc pred) args ⟨e⟩ chosen) next

private theorem malformedTransition (raw : Program 5) (p : Program 3)
    (out k prior c ty start cert cursor current : OTerm α)
    (known : Nonempty (Derivation body Γ (scratchGraph prior cursor current)))
    (broken : Nonempty (Derivation body Γ (malformed cursor)))
    (terminal : Nonempty (Derivation body Γ (scratchGraph out z z))) :
    Nonempty (Derivation body Γ (stepGraph raw p out k prior c ty start cert)) := by
  let args := call6 k prior c ty start cert
  obtain ⟨bad⟩ := broken
  have nz : Derivation body Γ (eqn cursor z).not := by
    simpa only [nonzero,equalEqn] using (Derivation.conjunctionLeft bad)
  obtain ⟨rule⟩ := openFailure body α cursor
  have reject : Nonempty (Derivation body Γ (unary cellGood z cursor)) :=
    closedApply ⟨Derivation.conjunctionRight rule⟩ ⟨Derivation.conjunctionRight bad⟩
  have rawCursor := (stateParts cursor current k prior c ty start cert known).1
  have inside := zeroBranchIntro (onCursor cellGood) dead (updateCell raw p) out args
    (atCursor cellGood z cursor args reject rawCursor) (deadGraph out args terminal)
  exact takeNonzero raw p out k prior c ty start cert cursor ⟨nz⟩ rawCursor inside

theorem malformedStep : OpenMalformedCollapse := by
  intro body raw p α out k prior c ty start cert cursor current
  let a := scratchGraph prior cursor current ⊓ (malformed cursor ⊓ scratchGraph out z z)
  have h : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have rhs := Derivation.conjunctionRight h
  obtain ⟨step⟩ := malformedTransition raw p out k prior c ty start cert cursor current
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionLeft rhs⟩ ⟨Derivation.conjunctionRight rhs⟩
  exact ⟨Derivation.implicationIntroduction step⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenMalformedProof
