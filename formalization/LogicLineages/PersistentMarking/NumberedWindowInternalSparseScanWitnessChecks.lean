module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (cell)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename witnessBinder witnessUnfold)
open NumberedWindowInternalSparseDirectedSeenOpenChecks (exact_OpenDirectedSeenWitness)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalSparseScanRetentionChecks (exact_ScanOnCons)
open NumberedWindowInternalSparseScanWitnessSyntaxProof
open NumberedWindowInternalSparseScanWitnessTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atNil (E : Program 4) (ctx ty w k : OTerm α) :
    Nonempty (Derivation body Γ (fromRow E z ctx ty w k)) := by
  let R := witnessRow E z ctx ty w k
  have h : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  have zero := nilRecover memberBase memberStep (suc z) (![w] : Fin 1 → OTerm α) ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨ne⟩ := valueUnique memberBase (suc z) z (![w] : Fin 1 → OTerm α) zero (zeroConstantValue _)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply ne))⟩

private theorem includeTest (A B C : Formula α) (d : Derivation body Γ (A ⊔ B)) :
    Nonempty (Derivation body Γ (A ⊔ (B ⊔ C))) := by
  have a : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have b : Derivation body (B :: Γ) B := Derivation.hypothesis List.mem_cons_self
  exact ⟨disjunctionElimination d (Derivation.implicationIntroduction (orLeft a))
    (Derivation.implicationIntroduction (orRight (orLeft b)))⟩

private theorem atCons (E : Program 4) (n h t ctx ty w k : OTerm α)
    (c : Derivation body Γ (cell n h t)) (ih : Derivation body Γ (fromRow E t ctx ty w k)) :
    Nonempty (Derivation body Γ (fromRow E n ctx ty w k)) := by
  let A := witnessRow E n ctx ty w k
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have cond := Derivation.conjunctionRight input
  obtain ⟨branches⟩ := consInversion n h t w ⟨addHyp c A⟩ ⟨Derivation.conjunctionLeft input⟩
  obtain ⟨law⟩ := exact_ScanOnCons E body α Δ n h t ctx ty k
  have useScan := Derivation.conjunctionRight (Derivation.implicationElimination law (addHyp c A))
  let L := (missGraph h w).not
  let R := memberGraph t w
  obtain ⟨eq⟩ := nonzeroEquality (body := body) (Γ := L :: Δ) h w (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨same⟩ := moveTest E ctx ty w h k (symm eq) (addHyp cond L)
  obtain ⟨head⟩ := includeTest (eqn h k) (acceptEdge E ctx ty h k) (scanGraph E t ctx ty k) same
  have left := Derivation.implicationElimination (addHyp useScan L) head
  have tail : Derivation body (R :: Δ) R := Derivation.hypothesis List.mem_cons_self
  have prior := Derivation.implicationElimination (addHyp (addHyp ih A) R) (Derivation.conjunctionIntroduction tail (addHyp cond R))
  have right := Derivation.implicationElimination (addHyp useScan R) (orRight (orRight prior))
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination branches
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right))⟩

private theorem constructor (E : Program 4) (ctx ty w k : OTerm α) :
    Nonempty (Derivation body Γ (constructors (motive E ctx ty w k))) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (constructorBody (motive E ctx ty w k))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := cell n h t
  let R := fromRow E t (ctx.relabel j) (ty.relabel j) (w.relabel j) (k.relabel j)
  let Δ := R :: C :: Γ.map (fun p => p.relabel j)
  change Nonempty (Derivation body (Γ.map (fun p => p.relabel j))
    (C.imp ((atIndex (motive E ctx ty w k) 2).imp (atIndex (motive E ctx ty w k) 0))))
  simp only [motiveIndex]
  obtain ⟨d⟩ := atCons (Γ := Δ) E n h t (ctx.relabel j) (ty.relabel j) (w.relabel j) (k.relabel j)
    (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exact_WitnessRowAcceptance : ExactWitnessRowAcceptance := by
  intro E body α Γ seen ctx ty w k
  have b : Nonempty (Derivation body Γ (atCode (motive E ctx ty w k) z)) := by rw [motiveAt]; exact atNil E ctx ty w k
  obtain ⟨b⟩ := b
  obtain ⟨c⟩ := constructor (body := body) (Γ := Γ) E ctx ty w k
  have d := actualOriginalListInductionAtCode body α Γ (motive E ctx ty w k) seen ⟨Derivation.conjunctionIntroduction b c⟩
  rw [motiveAt] at d
  exact d

theorem exact_OpenScanWitnessEquivalence : ExactOpenScanWitnessEquivalence := by
  intro E body α Γ seen ctx ty k
  obtain ⟨forward⟩ := exact_OpenDirectedSeenWitness E body α Γ seen ctx ty k
  let A := seenWitness E seen ctx ty k
  let Δ := A :: Γ
  let row := witnessBinder E seen ctx ty k
  let Θ := row :: Δ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨useRow⟩ := exact_WitnessRowAcceptance E body _ Θ (seen.relabel j) (ctx.relabel j) (ty.relabel j) w (k.relabel j)
  have result : Derivation body Θ (weaken (scanGraph E seen ctx ty k)) := by
    change Derivation body Θ ((scanGraph E seen ctx ty k).relabel j)
    rw [scanRename]
    exact Derivation.implicationElimination useRow (Derivation.hypothesis List.mem_cons_self)
  have d : Derivation body Δ (existsOne row) := (show Derivation body Δ A from Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction forward
    (Derivation.implicationIntroduction (Derivation.existentialElimination d result))⟩

#print axioms exact_WitnessRowAcceptance
#print axioms exact_OpenScanWitnessEquivalence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
