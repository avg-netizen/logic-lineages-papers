module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverNamedLeavesTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem addField (a b : Program 2) (x y : OTerm α) (xs : Fin 2 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph a x xs)))
    (right : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary fieldCons a b) (rawCons x y) xs)) := by
  apply compositionValue fieldCons (Fin.cons a (Fin.cons b Fin.elim0))
    (rawCons x y) xs ![x,y] (NumberedWindowInternalSparsePairGraphProof.consGraph x y)
  intro i
  exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i

private theorem report (tag : Nat) (ty i : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (namedCode tag) (namedTerm tag ty i) ![i,ty])) := by
  let xs : Fin 2 → OTerm α := ![i,ty]
  have last := addField (body := body) (Γ := Γ) (.projection 0) (constantZero 2)
    i z xs (projectionValue 0 xs) (zeroConstantValue xs)
  have typeField := addField (.projection 1) _ ty (rawCons i z) xs (projectionValue 1 xs) last
  exact addField (literal 2 tag) _ (numeral tag) (rawCons ty (rawCons i z)) xs
    (literalGraph tag xs) typeField

theorem singletonOrigin (tag : Nat) (ty i out key : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (singletonLeaf tag) out ![i,ty])))
    (hit : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (eqn (namedTerm tag ty i) key)) := by
  let xs : Fin 2 → OTerm α := ![i,ty]
  let n := namedTerm tag ty i
  have cell : Nonempty (Derivation body Γ (consGraph out n z)) := by
    apply compositionRecover consCode (Fin.cons (namedCode tag) (Fin.cons (constantZero 2) Fin.elim0))
      out xs ![n,z] h
    intro k
    exact Fin.cases (report tag ty i) (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) k
  obtain ⟨split⟩ := NumberedWindowInternalSparseFilterInclusionMemberConsProof.consInversion out n z key cell hit
  let H := (NumberedWindowInternalSparseFilterInclusionSyntaxProof.missGraph n key).not
  let T := memberGraph z key
  obtain ⟨same⟩ := NumberedWindowInternalSparseRoundWindowSingletonProof.nonzeroEquality
    (body := body) (Γ := H :: Γ) n key (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨impossible⟩ := NumberedWindowInternalCoverAscendingRangeOriginDataProof.nilHit
    (body := body) (Γ := T :: Γ) key ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction same)
    (Derivation.implicationIntroduction (Derivation.explosion impossible))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginDataProof
