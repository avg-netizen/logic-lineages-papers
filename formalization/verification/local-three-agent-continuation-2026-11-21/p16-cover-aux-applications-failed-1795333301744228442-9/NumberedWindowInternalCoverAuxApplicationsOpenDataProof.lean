module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem recoverReordered {m n : Nat} (P : Program m) (slots : Fin m → Fin n)
    (out : OTerm α) (xs : Fin n → OTerm α)
    (value : Nonempty (Derivation body Γ (programGraph (reorder P slots) out xs))) :
    Nonempty (Derivation body Γ (programGraph P out (fun i => xs (slots i)))) := by
  exact compositionRecover P (fun i => .projection (slots i)) out xs (fun i => xs (slots i))
    value (fun i => projectionValue (slots i) xs)

private theorem composeBinary {n : Nat} (P : Program 2) (a b : Program n)
    (out x y : OTerm α) (xs : Fin n → OTerm α)
    (call : Nonempty (Derivation body Γ (programGraph P out ![x,y])))
    (left : Nonempty (Derivation body Γ (programGraph a x xs)))
    (right : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary P a b) out xs)) := by
  apply compositionValue P (Fin.cons a (Fin.cons b Fin.elim0)) out xs ![x,y] call
  intro i
  exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i

private theorem addField (a b : Program 4) (x y : OTerm α) (xs : Fin 4 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph a x xs)))
    (right : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary fieldCons a b) (rawCons x y) xs)) :=
  composeBinary fieldCons a b (rawCons x y) x y xs (NumberedWindowInternalSparsePairGraphProof.consGraph x y) left right

private theorem nodeReport (dom cod fn arg : OTerm α) :
    Nonempty (Derivation body Γ (programGraph auxCode (auxiliaryTerm dom cod fn arg) ![arg,dom,cod,fn])) := by
  let xs : Fin 4 → OTerm α := ![arg,dom,cod,fn]
  have last := addField (body := body) (Γ := Γ) (.projection 0) (constantZero 4) arg z xs (projectionValue 0 xs) (zeroConstantValue xs)
  have bodyFn := addField (.projection 3) _ fn (rawCons arg z) xs (projectionValue 3 xs) last
  have bodyCod := addField (.projection 2) _ cod (rawCons fn (rawCons arg z)) xs (projectionValue 2 xs) bodyFn
  have bodyDom := addField (.projection 1) _ dom (rawCons cod (rawCons fn (rawCons arg z))) xs
    (projectionValue 1 xs) bodyCod
  exact addField (literal 4 6) _ (numeral 6) (rawCons dom (rawCons cod (rawCons fn (rawCons arg z)))) xs
    (literalGraph 6 xs) bodyDom

theorem singletonMember (dom cod fn arg out : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph singletonAux out ![arg,dom,cod,fn]))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg))) := by
  let xs : Fin 4 → OTerm α := ![arg,dom,cod,fn]
  let n := auxiliaryTerm dom cod fn arg
  have head := nodeReport (body := body) (Γ := Γ) dom cod fn arg
  have cons : Nonempty (Derivation body Γ (consGraph out n z)) := by
    apply compositionRecover consCode (Fin.cons auxCode (Fin.cons (constantZero 4) Fin.elim0))
      out xs ![n,z] h
    intro i
    exact Fin.cases head (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) i
  exact headMember out n z n cons ⟨refl n⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
