module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
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
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverAuxApplicationsTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

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

theorem singletonCell (one d c f a : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph singletonAux one ![a,d,c,f]))) :
    Nonempty (Derivation body Γ (consGraph one (auxiliaryTerm d c f a) z)) := by
  let xs : Fin 4 → OTerm α := ![a,d,c,f]
  apply compositionRecover consCode (Fin.cons auxCode (Fin.cons (constantZero 4) Fin.elim0))
    one xs ![auxiliaryTerm d c f a,z] run
  intro i
  exact Fin.cases (nodeReport d c f a) (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) i

theorem outerGraph (out K T : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph auxApplications out ![K,T]))) :
    Nonempty (Derivation body Γ (flatGraph codAxis out K ![K,T])) := by
  have moved := recoverReordered (flatMap codAxis) (![0,0,1] : Fin 3 → Fin 2)
    out ![K,T] run
  have tape : (fun i => (![K,T] : Fin 2 → OTerm α) ((![0,0,1] : Fin 3 → Fin 2) i)) = Fin.cons K ![K,T] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromDomain (out d K T : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph codAxis out ![d,K,T]))) :
    Nonempty (Derivation body Γ (flatGraph fnAxis out K ![K,T,d])) := by
  have moved := recoverReordered (flatMap fnAxis) (![1,1,2,0] : Fin 4 → Fin 3)
    out ![d,K,T] run
  have tape : (fun i => (![d,K,T] : Fin 3 → OTerm α) ((![1,1,2,0] : Fin 4 → Fin 3) i)) = Fin.cons K ![K,T,d] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromCodomain (out c K T d : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph fnAxis out ![c,K,T,d]))) :
    Nonempty (Derivation body Γ (flatGraph argAxis out T ![T,d,c])) := by
  have moved := recoverReordered (flatMap argAxis) (![2,2,3,0] : Fin 4 → Fin 4)
    out ![c,K,T,d] run
  have tape : (fun i => (![c,K,T,d] : Fin 4 → OTerm α) ((![2,2,3,0] : Fin 4 → Fin 4) i)) = Fin.cons T ![T,d,c] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromFunction (out f T d c : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph argAxis out ![f,T,d,c]))) :
    Nonempty (Derivation body Γ (flatGraph singletonAux out T ![d,c,f])) := by
  have moved := recoverReordered (flatMap singletonAux) (![1,2,3,0] : Fin 4 → Fin 4)
    out ![f,T,d,c] run
  have tape : (fun i => (![f,T,d,c] : Fin 4 → OTerm α) ((![1,2,3,0] : Fin 4 → Fin 4) i)) = Fin.cons T ![d,c,f] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOpenDataProof
