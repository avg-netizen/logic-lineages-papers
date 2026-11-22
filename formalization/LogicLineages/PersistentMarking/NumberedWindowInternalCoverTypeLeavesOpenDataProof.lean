module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverTypeLeavesTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem emptyTapeRename {β : Type} (j : α → β) :
    (fun i : Fin 0 => (Fin.elim0 i : OTerm α).relabel j) = (Fin.elim0 : Fin 0 → OTerm β) := by
  funext i
  exact Fin.elim0 i

theorem oneTapeRename {β : Type} (ty : OTerm α) (j : α → β) :
    (fun i : Fin 1 => ((unaryTape ty) i).relabel j) = unaryTape (ty.relabel j) := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem reportRename {β : Type} (out K : OTerm α) (j : α → β) :
    (typeLeavesReport out K).relabel j = typeLeavesReport (out.relabel j) (K.relabel j) := by
  simp only [typeLeavesReport,programRename,oneTapeRename]

theorem termRename {β : Type} (ty : OTerm α) (j : α → β) :
    (typeLeafTerm ty).relabel j = typeLeafTerm (ty.relabel j) := by
  simp only [typeLeafTerm,rawConsRename,zRelabel,numeralRename]

private theorem attach (a b : Program 1) (x y : OTerm α) (xs : Fin 1 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph a x xs)))
    (right : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary fieldCons a b) (rawCons x y) xs)) := by
  apply compositionValue fieldCons (Fin.cons a (Fin.cons b Fin.elim0))
    (rawCons x y) xs ![x,y] (NumberedWindowInternalSparsePairGraphProof.consGraph x y)
  intro i
  exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i

theorem nodeReport (ty : OTerm α) :
    Nonempty (Derivation body Γ (programGraph typeLeafCode (typeLeafTerm ty) (unaryTape ty))) := by
  let xs := unaryTape ty
  have last := attach (body := body) (Γ := Γ) (.projection 0) (constantZero 1)
    ty z xs (projectionValue 0 xs) (zeroConstantValue xs)
  exact attach (literal 1 3) _ (numeral 3) (rawCons ty z) xs (literalGraph 3 xs) last

theorem singletonCell (one ty : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph typeLeafSingleton one (unaryTape ty)))) :
    Nonempty (Derivation body Γ (consGraph one (typeLeafTerm ty) z)) := by
  let xs := unaryTape ty
  apply compositionRecover consCode (Fin.cons typeLeafCode (Fin.cons (constantZero 1) Fin.elim0))
    one xs ![typeLeafTerm ty,z] run
  intro i
  exact Fin.cases (nodeReport ty) (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) i

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
