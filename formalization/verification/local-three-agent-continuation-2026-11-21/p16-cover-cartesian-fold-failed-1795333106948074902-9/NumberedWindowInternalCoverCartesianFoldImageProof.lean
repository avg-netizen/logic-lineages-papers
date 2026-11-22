module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldImageProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets

attribute [local irreducible] programGraph

variable {k : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem collectValue (D : Program (k+1)) (out raw image : OTerm α) (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Γ (flatGraph D out raw params))) :
    Nonempty (Derivation body Γ (programGraph (collected D) out (Fin.cons raw (Fin.cons image params)))) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons raw (Fin.cons image params)
  apply compositionValue (flatMap D) (Fin.cons (.projection 0) (fun i => .projection i.succ.succ))
    out xs (Fin.cons raw params) h
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact projectionValue 0 xs
  · exact projectionValue j.succ.succ xs

theorem imageOfMember (D : Program (k+1)) (out raw image : OTerm α) (params : Fin k → OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph D out raw params)))
    (member : Nonempty (Derivation body Γ (memberGraph out image))) :
    Nonempty (Derivation body Γ (imageGraph D raw image params)) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons raw (Fin.cons image params)
  apply compositionValue scratchMember ![collected D,.projection 1] (suc z) xs ![out,image] member
  intro i
  exact Fin.cases (collectValue D out raw image params run)
    (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i

theorem memberOfImage (D : Program (k+1)) (out raw image : OTerm α) (params : Fin k → OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph D out raw params)))
    (member : Nonempty (Derivation body Γ (imageGraph D raw image params))) :
    Nonempty (Derivation body Γ (memberGraph out image)) := by
  let xs : Fin (k+2) → OTerm α := Fin.cons raw (Fin.cons image params)
  apply compositionRecover scratchMember ![collected D,.projection 1] (suc z) xs ![out,image] member
  intro i
  exact Fin.cases (collectValue D out raw image params run)
    (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldImageProof
