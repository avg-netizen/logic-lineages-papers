module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverNumberedLayerTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem quintInputsRename {β : Type} (a b c d e : OTerm α) (j : α → β) :
    (fun i : Fin 5 => ((![a,b,c,d,e] : Fin 5 → OTerm α) i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j] := by
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l =>
    Fin.cases ?_ (fun m => Fin.cases ?_ (fun n => Fin.cases ?_ (fun u => Fin.elim0 u) n) m) l) k) i <;> rfl

theorem numberedRename {β : Type} (h ty k l r : OTerm α) (j : α → β) :
    (numberedTerm h ty k l r).relabel j =
      numberedTerm (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) := by
  simp only [numberedTerm,rawConsRename,zRelabel,numeralRename]

private theorem attach (a b : Program 5) (x y : OTerm α) (xs : Fin 5 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph a x xs)))
    (right : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary fieldCons a b) (rawCons x y) xs)) := by
  apply compositionValue fieldCons (Fin.cons a (Fin.cons b Fin.elim0))
    (rawCons x y) xs ![x,y] (NumberedWindowInternalSparsePairGraphProof.consGraph x y)
  intro i
  exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i

theorem nodeReport (h ty k l r : OTerm α) :
    Nonempty (Derivation body Γ (programGraph numberedCode (numberedTerm h ty k l r) ![r,h,ty,k,l])) := by
  let xs : Fin 5 → OTerm α := ![r,h,ty,k,l]
  let sr := rawCons r z
  let sl := rawCons l sr
  let sk := rawCons k sl
  let st := rawCons ty sk
  let sh := rawCons h st
  have last := attach (body := body) (Γ := Γ) (.projection 0) (constantZero 5)
    r z xs (projectionValue 0 xs) (zeroConstantValue xs)
  have left := attach (.projection 4) _ l sr xs (projectionValue 4 xs) last
  have pos := attach (.projection 3) _ k sl xs (projectionValue 3 xs) left
  have typ := attach (.projection 2) _ ty sk xs (projectionValue 2 xs) pos
  have head := attach (.projection 1) _ h st xs (projectionValue 1 xs) typ
  exact attach (literal 5 5) _ (numeral 5) sh xs (literalGraph 5 xs) head

theorem singletonCell (one h ty k l r : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph singletonNumbered one ![r,h,ty,k,l]))) :
    Nonempty (Derivation body Γ (consGraph one (numberedTerm h ty k l r) z)) := by
  let xs : Fin 5 → OTerm α := ![r,h,ty,k,l]
  apply compositionRecover consCode (Fin.cons numberedCode (Fin.cons (constantZero 5) Fin.elim0))
    one xs ![numberedTerm h ty k l r,z] run
  intro i
  exact Fin.cases (nodeReport h ty k l r) (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) i

theorem outerGraph (out H K ids args : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph numberedLayer out ![H,K,ids,args]))) :
    Nonempty (Derivation body Γ (flatGraph headBlock out H ![K,ids,args])) := by
  have moved := run
  have tape : (![H,K,ids,args] : Fin 4 → OTerm α) = Fin.cons H ![K,ids,args] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromHead (out h K ids args : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph headBlock out ![h,K,ids,args]))) :
    Nonempty (Derivation body Γ (flatGraph typeBlock out K ![ids,args,h])) := by
  have moved := recoverReordered (flatMap typeBlock) (![1,2,3,0] : Fin 4 → Fin 4)
    out ![h,K,ids,args] run
  have tape : (fun i => (![h,K,ids,args] : Fin 4 → OTerm α) ((![1,2,3,0] : Fin 4 → Fin 4) i)) = Fin.cons K ![ids,args,h] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromType (out ty ids args h : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph typeBlock out ![ty,ids,args,h]))) :
    Nonempty (Derivation body Γ (flatGraph idBlock out ids ![args,h,ty])) := by
  have moved := recoverReordered (flatMap idBlock) (![1,2,3,0] : Fin 4 → Fin 4)
    out ![ty,ids,args,h] run
  have tape : (fun i => (![ty,ids,args,h] : Fin 4 → OTerm α) ((![1,2,3,0] : Fin 4 → Fin 4) i)) = Fin.cons ids ![args,h,ty] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.elim0 u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromId (out k args h ty : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph idBlock out ![k,args,h,ty]))) :
    Nonempty (Derivation body Γ (flatGraph prefixBlock out args ![args,h,ty,k])) := by
  have moved := recoverReordered (flatMap prefixBlock) (![1,1,2,3,0] : Fin 5 → Fin 4)
    out ![k,args,h,ty] run
  have tape : (fun i => (![k,args,h,ty] : Fin 4 → OTerm α) ((![1,1,2,3,0] : Fin 5 → Fin 4) i)) = Fin.cons args ![args,h,ty,k] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.cases rfl (fun v => Fin.elim0 v) u) l) k) j) i
  rw [tape] at moved
  exact moved

theorem fromPrefix (out l args h ty k : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph prefixBlock out ![l,args,h,ty,k]))) :
    Nonempty (Derivation body Γ (flatGraph singletonNumbered out args ![h,ty,k,l])) := by
  have moved := recoverReordered (flatMap singletonNumbered) (![1,2,3,4,0] : Fin 5 → Fin 5)
    out ![l,args,h,ty,k] run
  have tape : (fun i => (![l,args,h,ty,k] : Fin 5 → OTerm α) ((![1,2,3,4,0] : Fin 5 → Fin 5) i)) = Fin.cons args ![h,ty,k,l] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun u => Fin.cases rfl (fun v => Fin.elim0 v) u) l) k) j) i
  rw [tape] at moved
  exact moved

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
