module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseMemberConsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exact open membership constructor branch: where the head does not match,
a real selected occurrence must be in the original scratch tail. -/
theorem memberTailOfMismatch (raw head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph raw head tail)))
    (hm : Nonempty (Derivation body Delta (memberGraph raw needle)))
    (hn : Nonempty (Derivation body Delta (eqn head needle).not)) :
    Nonempty (Derivation body Delta (memberGraph tail needle)) := by
  let H := (missGraph head needle).not
  let T := memberGraph tail needle
  obtain ⟨choice⟩ := consInversion raw head tail needle hc hm
  obtain ⟨no⟩ := hn
  have hhit : Derivation body (H :: Delta) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨he⟩ := equalityOfHit head needle ⟨hhit⟩
  have hitImpossible : Derivation body Delta (H.imp T) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp no H) he))
  have keep : Derivation body Delta (T.imp T) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination choice hitImpossible keep⟩

/-- Mismatch/zero-tail-bit cannot be the current member's erase branch.
The induction hypothesis is the actual tail membership implication. -/
theorem absentBranchImpossible (raw head tail needle priorBit : OTerm alpha) (goal : Formula alpha)
    (hc : Nonempty (Derivation body Delta (consGraph raw head tail)))
    (hm : Nonempty (Derivation body Delta (memberGraph raw needle)))
    (hn : Nonempty (Derivation body Delta (eqn head needle).not))
    (hzero : Nonempty (Derivation body Delta (eqn priorBit z)))
    (ih : Nonempty (Derivation body Delta ((memberGraph tail needle).imp (eqn priorBit (suc z))))) :
    Nonempty (Derivation body Delta goal) := by
  obtain ⟨ht⟩ := memberTailOfMismatch raw head tail needle hc hm hn
  obtain ⟨hz⟩ := hzero
  obtain ⟨h⟩ := ih
  exact ⟨Derivation.explosion (sucNeZeroApply
    (InternalTagArithmeticSupportProof.trans (symm (Derivation.implicationElimination h ht)) hz))⟩

#print axioms memberTailOfMismatch
#print axioms absentBranchImpossible
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseMemberConsProof
