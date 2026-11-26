module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountMemberProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm graph)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRawListRecursionProof (nilValue)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem headEqual (h k : OTerm α) (hit : Derivation body Γ (missGraph h k).not) :
    Nonempty (Derivation body Γ (eqn h k)) := by
  obtain ⟨comparison⟩ := actualOriginalComparison body α h k
  have split := compareView (weakenClosed comparison Γ)
  let L := ltF h k
  let R := ltF k h
  let M := eqn h k
  obtain ⟨noLeft⟩ := rejectForwardOrder (body := body) (Gamma := L :: Γ) h k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨noRight⟩ := rejectBackwardOrder (body := body) (Gamma := R :: Γ) h k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have left : Derivation body Γ (L.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp hit L) noLeft))
  have right : Derivation body Γ (R.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp hit R) noRight))
  have same : Derivation body Γ (M.imp M) := Derivation.implicationIntroduction
    (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination split left (Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp same (M ⊔ R)) (addHyp right (M ⊔ R))))⟩

theorem poolMember (pool seed candidate : OTerm α)
    (hp : Nonempty (Derivation body Γ (memberGraph pool seed)))
    (he : Nonempty (Derivation body Γ (eqn candidate seed))) :
    Nonempty (Derivation body Γ (memberGraph pool candidate)) := by
  obtain ⟨he⟩ := he
  unfold memberGraph programGraph at hp ⊢
  apply graphInputTransport body α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember)
    (suc z) ![pool,seed] ![pool,candidate] _ hp
  intro i
  simp only [onEquality]
  exact Fin.cases (Nonempty.intro (refl pool))
    (Fin.cases (Nonempty.intro (symm he)) (fun k => Fin.elim0 k)) i

theorem missRecover (raw head tail candidate : OTerm α)
    (hc : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (different : Nonempty (Derivation body Γ (eqn head candidate).not))
    (hit : Nonempty (Derivation body Γ (memberGraph raw candidate))) :
    Nonempty (Derivation body Γ (memberGraph tail candidate)) := by
  obtain ⟨alternatives⟩ := consInversion raw head tail candidate hc hit
  obtain ⟨notEq⟩ := different
  let A := (missGraph head candidate).not
  let B := memberGraph tail candidate
  obtain ⟨same⟩ := headEqual (body := body) (Γ := A :: Γ) head candidate
    (Derivation.hypothesis List.mem_cons_self)
  have first : Derivation body Γ (A.imp B) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp notEq A) same))
  have second : Derivation body Γ (B.imp B) := Derivation.implicationIntroduction
    (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination alternatives first second⟩

theorem memberNil (candidate : OTerm α) :
    Nonempty (Derivation body Γ (programGraph scratchMember z ![z,candidate])) :=
  nilValue memberBase memberStep z (![candidate] : Fin 1 → OTerm α) (zeroConstantValue _)

#print axioms poolMember
#print axioms missRecover
#print axioms memberNil
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountMemberProof
