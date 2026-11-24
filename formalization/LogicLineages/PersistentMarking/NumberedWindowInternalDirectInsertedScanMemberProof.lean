module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMember
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow oneTerm)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanCons)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalDirectInsertedScanMemberTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilFalse (k : OrdinaryArithmetic.Term α)
    (member : Nonempty (Derivation B Γ (memberGraph z k))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have impossible := nilRecover memberBase memberStep (suc z) ![k] member
  have zero : Nonempty (Derivation B Γ (programGraph memberBase z ![k])) :=
    constantZeroValue ![k]
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![k] impossible zero
  exact ⟨sucNeZeroApply bad⟩

private theorem headChange (r : Program 3) (removed h k : OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation B Γ (eqn h k)))
    (row : Nonempty (Derivation B Γ (rowAccept r h removed))) :
    Nonempty (Derivation B Γ (rowAccept r k removed)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := ![removed,h]
  let ys : Fin 2 → OrdinaryArithmetic.Term α := ![removed,k]
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula (insertedRow r))
    oneTerm xs ys _ row
  intro j
  refine Fin.cases ?_ (fun l => ?_) j
  · change Nonempty (Derivation B Γ (equal removed removed))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl removed⟩
  · obtain rfl := Fin.eq_zero l
    change Nonempty (Derivation B Γ (equal h k))
    rw [equalEqn]
    exact he

private theorem nilLaw (r : Program 3) (removed k : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (fromMember r z removed k)) := by
  let H := loopAccept r z removed ⊓ memberGraph z k
  have h : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨f⟩ := nilFalse k ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion f)⟩

private theorem consApply (r : Program 3) (code h tail removed k : OrdinaryArithmetic.Term α)
    (cons : Nonempty (Derivation B Γ (consGraph code h tail)))
    (tailLaw : Nonempty (Derivation B Γ (fromMember r tail removed k)))
    (accepted : Nonempty (Derivation B Γ (loopAccept r code removed)))
    (member : Nonempty (Derivation B Γ (memberGraph code k))) :
    Nonempty (Derivation B Γ (rowAccept r k removed)) := by
  obtain ⟨both⟩ := exactOpenScanCons r B α Γ code h tail removed cons accepted
  obtain ⟨split⟩ := consInversion code h tail k cons member
  obtain ⟨ih⟩ := tailLaw
  let L := (missGraph h k).not
  let R := memberGraph tail k
  have leftWitness : Nonempty (Derivation B Γ (L.imp (rowAccept r k removed))) := by
    have same := equalityOfHit h k (body := B) (Γ := L :: Γ)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨p⟩ := headChange r removed h k same
      ⟨addHyp (Derivation.conjunctionLeft both) L⟩
    exact ⟨Derivation.implicationIntroduction p⟩
  obtain ⟨left⟩ := leftWitness
  have right : Derivation B Γ (R.imp (rowAccept r k removed)) := by
    have pair : Derivation B (R :: Γ) (loopAccept r tail removed ⊓ memberGraph tail k) :=
      Derivation.conjunctionIntroduction (addHyp (Derivation.conjunctionRight both) R)
        (Derivation.hypothesis List.mem_cons_self)
    exact Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp ih R) pair)
  exact ⟨disjunctionElimination split left right⟩

private theorem consLaw (r : Program 3) (code h tail removed k : OrdinaryArithmetic.Term α)
    (cell : Nonempty (Derivation B Γ (consGraph code h tail)))
    (tailLaw : Nonempty (Derivation B Γ (fromMember r tail removed k))) :
    Nonempty (Derivation B Γ (fromMember r code removed k)) := by
  let H := loopAccept r code removed ⊓ memberGraph code k
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨c⟩ := cell
  obtain ⟨t⟩ := tailLaw
  obtain ⟨result⟩ := consApply r code h tail removed k ⟨addHyp c H⟩ ⟨addHyp t H⟩
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction result⟩

private theorem constructorLaw (r : Program 3) (removed k : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation B Γ (constructors (invariant r removed k))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (invariant r removed k))
  let ρ : α → α ⊕ Fin 3 := Sum.inl
  let n : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  let h : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 1)
  let t : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := fromMember r t (removed.relabel ρ) (k.relabel ρ)
  let Δ := R :: C :: Γ.map (fun p => p.relabel ρ)
  change Nonempty (Derivation B (Γ.map (fun p => p.relabel ρ))
    (C.imp ((atIndex (invariant r removed k) 2).imp (atIndex (invariant r removed k) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := consLaw (B := B) (Γ := Δ) r n h t (removed.relabel ρ) (k.relabel ρ)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exactOpenScanMember : ExactOpenScanMember := by
  intro r body α Γ code removed k
  have base : Nonempty (Derivation body Γ (atCode (invariant r removed k) z)) := by
    rw [invariantCode]
    exact nilLaw r removed k
  obtain ⟨start⟩ := base
  obtain ⟨step⟩ := constructorLaw (B := body) (Γ := Γ) r removed k
  have all : Nonempty (Derivation body Γ (premises (invariant r removed k))) :=
    ⟨Derivation.conjunctionIntroduction start step⟩
  have atRaw := actualOriginalListInductionAtCode body α Γ (invariant r removed k) code all
  rw [invariantCode] at atRaw
  exact atRaw

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMember
