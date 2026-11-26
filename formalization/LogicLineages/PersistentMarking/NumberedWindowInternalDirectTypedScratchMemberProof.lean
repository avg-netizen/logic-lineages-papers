module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectTypedScratchConsProof (exact_TypedScratchCons)
open NumberedWindowInternalDirectTypedScratchMemberTargets
open NumberedWindowInternalDirectTypedScratchMemberSyntaxProof (invariantCode invariantIndex)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilLaw (i : Program 1) (key : OTerm α) :
    Nonempty (Derivation B Γ (fromMember i z key)) := by
  let H := unary (typedScratch i) (suc z) z ⊓ memberGraph z key
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have ran := nilRecover memberBase memberStep (suc z) ![key] ⟨Derivation.conjunctionRight own⟩
  have zero : Nonempty (Derivation B (H :: Γ) (programGraph memberBase z ![key])) :=
    constantZeroValue ![key]
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![key] ran zero
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad))⟩

private theorem consApply (i : Program 1) (code h tail key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code h tail)))
    (tailLaw : Nonempty (Derivation B Γ (fromMember i tail key)))
    (typed : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code)))
    (member : Nonempty (Derivation B Γ (memberGraph code key))) :
    Nonempty (Derivation B Γ (unary i (suc z) key)) := by
  obtain ⟨both⟩ := exact_TypedScratchCons i B α Γ code h tail cell typed
  obtain ⟨split⟩ := consInversion code h tail key cell member
  obtain ⟨ih⟩ := tailLaw
  let L := (missGraph h key).not
  let R := memberGraph tail key
  have leftPrem : Nonempty (Derivation B Γ (L.imp (unary i (suc z) key))) := by
    have same := equalityOfHit h key (body := B) (Γ := L :: Γ)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨scalar⟩ := moveUnary i (suc z) h key same ⟨addHyp (Derivation.conjunctionLeft both) L⟩
    exact ⟨Derivation.implicationIntroduction scalar⟩
  obtain ⟨left⟩ := leftPrem
  have right : Derivation B Γ (R.imp (unary i (suc z) key)) := by
    have input : Derivation B (R :: Γ) (unary (typedScratch i) (suc z) tail ⊓ memberGraph tail key) :=
      Derivation.conjunctionIntroduction (addHyp (Derivation.conjunctionRight both) R)
        (Derivation.hypothesis List.mem_cons_self)
    exact Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp ih R) input)
  exact ⟨disjunctionElimination split left right⟩

private theorem consLaw (i : Program 1) (code h tail key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code h tail)))
    (tailLaw : Nonempty (Derivation B Γ (fromMember i tail key))) :
    Nonempty (Derivation B Γ (fromMember i code key)) := by
  let H := unary (typedScratch i) (suc z) code ⊓ memberGraph code key
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨c⟩ := cell
  obtain ⟨t⟩ := tailLaw
  obtain ⟨out⟩ := consApply i code h tail key ⟨addHyp c H⟩ ⟨addHyp t H⟩
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction out⟩

private theorem constructorLaw (i : Program 1) (key : OTerm α) :
    Nonempty (Derivation B Γ (constructors (invariant i key))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (invariant i key))
  let ρ : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := fromMember i t (key.relabel ρ)
  let Δ := R :: C :: Γ.map (fun p => p.relabel ρ)
  change Nonempty (Derivation B (Γ.map (fun p => p.relabel ρ))
    (C.imp ((atIndex (invariant i key) 2).imp (atIndex (invariant i key) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := consLaw (B := B) (Γ := Δ) i n h t (key.relabel ρ)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exact_TypedScratchMember : ExactTypedScratchMember := by
  intro i body α Γ code key
  have base : Nonempty (Derivation body Γ (atCode (invariant i key) z)) := by
    rw [invariantCode]
    exact nilLaw i key
  obtain ⟨start⟩ := base
  obtain ⟨step⟩ := constructorLaw (B := body) (Γ := Γ) i key
  have all : Nonempty (Derivation body Γ (premises (invariant i key))) :=
    ⟨Derivation.conjunctionIntroduction start step⟩
  have atRaw := actualOriginalListInductionAtCode body α Γ (invariant i key) code all
  rw [invariantCode] at atRaw
  exact atRaw

#print axioms exact_TypedScratchMember
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
