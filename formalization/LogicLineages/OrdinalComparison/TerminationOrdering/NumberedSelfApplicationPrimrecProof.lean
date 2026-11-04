module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationPrimrecProof
open Source Source.SourceSpecialApplication NumberedAuxiliaryCoding NumberedSelfApplication

attribute [local irreducible] Primrec

theorem arrowsPrimitive : NumberedSelfApplicationTargets.ActualArrowsPrimitive := by
  have hs : Primrec (fun p : (List Ty × Ty) × (Ty × Ty) => Ty.arrow p.2.1 p.2.2) :=
    NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr Primrec.fst Primrec.snd hs.to₂
  apply h.of_eq
  rintro ⟨types,tau⟩
  induction types with
  | nil => rfl
  | cons sigma types ih => exact congrArg (Ty.arrow sigma) ih

def selfNode {Symbol : Type} (p : SelfData Symbol × Ty) : Code Symbol :=
  .numbered p.1.1 p.1.2.1 p.2 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2

theorem selfNodePrimitive (n : Nat) : Primrec (@selfNode (Fin n)) := by
  have h2 : Primrec (fun p : SelfData (Fin n) × Ty => p.1.2) := Primrec.snd.comp Primrec.fst
  have h3 := Primrec.snd.comp h2
  have h4 := Primrec.snd.comp h3
  exact (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp h2).pair (Primrec.snd.pair
      ((Primrec.fst.comp h3).pair ((Primrec.fst.comp h4).pair (Primrec.snd.comp h4))))))

theorem selfEntriesPrimitive : NumberedSelfApplicationTargets.ActualSelfEntriesPrimitive := by
  intro n
  have he : Primrec (fun p : (SelfData (Fin n) × List Ty) × Ty => (p.2,selfNode (p.1.1,p.2))) :=
    Primrec.snd.pair ((selfNodePrimitive n).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
  exact Primrec.list_map Primrec.snd he.to₂

theorem selfCodePrimitive : NumberedSelfApplicationTargets.ActualSelfCodePrimitive := by
  intro n
  have hn : Primrec (fun p : (SelfData (Fin n) × List Ty) × (Ty × Code (Fin n)) => selfNode (p.1.1,p.2.1)) :=
    (selfNodePrimitive n).comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hs : Primrec (fun p : (SelfData (Fin n) × List Ty) × (Ty × Code (Fin n)) =>
      Code.argumentsCons p.2.1 (selfNode (p.1.1,p.2.1)) p.2.2) :=
    (NumberedCodeAssemblyPrimrecProof.argumentsConsPrimitive n).comp
      ((Primrec.fst.comp Primrec.snd).pair (hn.pair (Primrec.snd.comp Primrec.snd)))
  have h := Primrec.list_foldr Primrec.snd (Primrec.const Code.argumentsNil) hs.to₂
  apply h.of_eq
  rintro ⟨d,types⟩
  induction types with
  | nil => rfl
  | cons sigma types ih => exact congrArg (Code.argumentsCons sigma (selfNode (d,sigma))) ih

theorem applicationPrimitive : NumberedSelfApplicationTargets.ActualApplicationPrimitive := by
  intro n
  have hs : Primrec (fun p : (Code (Fin n) × List (Ty × Code (Fin n))) × (Code (Fin n) × (Ty × Code (Fin n))) =>
      Code.app p.2.2.1 p.2.1 p.2.2.2) :=
    (NumberedCodeAssemblyPrimrecProof.appPrimitive n).comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.list_foldl Primrec.snd Primrec.fst hs.to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationPrimrecProof
