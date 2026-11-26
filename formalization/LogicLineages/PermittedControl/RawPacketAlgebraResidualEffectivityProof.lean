module
public import LogicLineages.PermittedControl.RawPacketAlgebraResidualTargets
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof
import LogicLineages.PermittedControl.RawPacketAlgebraGuardProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open MixedSameRankResidue (WeightedCode)
open HeterogeneousSignedMatrixSlice (TestCode RawRow)

private theorem optionTraverse {σ α β : Type} [Primcodable σ] [Primcodable α] [Primcodable β]
    {g : σ → α → Option β} (hg : Primrec₂ g) :
    Primrec₂ (fun (s : σ) (xs : List α) =>
      xs.foldr (fun x acc => (g s x).bind (fun y => acc.map (List.cons y))) (some [])) := by
  have hh : Primrec₂ (fun (q : σ × List α) (p : α × Option (List β)) =>
      (g q.1 p.1).bind (fun y => p.2.map (List.cons y))) :=
    Primrec.option_bind (hg.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact Primrec.list_foldr Primrec.snd (Primrec.const (some [])) hh

private theorem filterAsMap {β : Type} (p : β → Bool) : ∀ xs : List β,
    xs.filterMap (fun x => bif p x then some x else none) = xs.filter p
  | [] => rfl
  | x :: xs => by
    cases h : p x
    · simp [List.filterMap_cons,List.filter_cons,h,filterAsMap p xs]
    · simp [List.filterMap_cons,List.filter_cons,h,filterAsMap p xs]

theorem decodeTermPrimitive : Primrec₂ decodeTermCode := by
  let A := List LowerOperandCode × TermData
  have tag : Primrec (fun q : A => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have name : Primrec (fun q : A => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have c : Primrec (fun q : A => decide (q.2.2.1 = 0) && !decide (q.2.2.2.1 = 0)) :=
    Primrec.and.comp ((Primrec.eq.comp tag (Primrec.const 0)).decide)
      (Primrec.not.comp ((Primrec.eq.comp name (Primrec.const 0)).decide))
  have get : Primrec (fun q : A => q.1[q.2.2.2.1 - 1]?) :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.nat_sub.comp name (Primrec.const 1))
  have mapped : Primrec (fun q : A => (q.1[q.2.2.2.1 - 1]?).map (fun op => (q.2.1,op))) :=
    Primrec.option_map get ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact Primrec.cond c mapped (Primrec.const none)

theorem decodeTermsPrimitive : Primrec₂ decodeTermsCode :=
  (optionTraverse decodeTermPrimitive).of_eq (fun _ _ => rfl)

theorem testOfPrimitive : Primrec testOfCode :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const (1,0))
    ((Primrec.const 3).pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))

theorem decodeRowPrimitive : Primrec₂ decodeRowCode := by
  let A := List LowerOperandCode × NormalForm.Code.AtomData
  have terms : Primrec (fun q : A => decodeTermsCode q.1 q.2.2.2.2) :=
    decodeTermsPrimitive.comp Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have g : Primrec₂ (fun (q : A) (ts : List WeightedCode) => (testOfCode q.2,q.2.2.2.1,ts)) :=
    (testOfPrimitive.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
        Primrec.snd)
  exact Primrec.option_map terms g

theorem decodeAtomPrimitive : Primrec₂ decodeAtomCode :=
  decodeRowPrimitive.comp Primrec.fst (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd)

theorem decodeAtomsPrimitive : Primrec₂ decodeAtomsCode :=
  (optionTraverse decodeAtomPrimitive).of_eq (fun _ _ => rfl)

theorem decodePrimitive : Primrec₂ decodeCode :=
  decodeAtomsPrimitive.comp Primrec.fst (LinearRowsCodeProof.atoms_primitive.comp Primrec.snd)

theorem residualOfPrimitive : Primrec residualOf := by
  have rows : Primrec (fun o : PreparedPacketCode => decodeCode (tableOf o.1) o.2) :=
    decodePrimitive.comp (tablePrimitive.comp Primrec.fst) Primrec.snd
  have g : Primrec₂ (fun (o : PreparedPacketCode) (rs : List RawRow) => (tableOf o.1,o.2,rs)) :=
    (tablePrimitive.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.option_map rows g

theorem decodeRoutePrimitive : Primrec₂ decodeRouteCode :=
  residualOfPrimitive.comp projectPrimitive

theorem keepPredicatePrimitive :
    Primrec₂ (fun (top : Nat) (c : PreparedPacketCode) =>
      (tableOf c.1).all (fun op => decide (op.2.1 < top))) := by
  have hp : Primrec₂ (fun (top : Nat) (op : LowerOperandCode) => decide (op.2.1 < top)) :=
    (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst).decide
  exact (LinearRowsCodeProof.listAll_primitive hp).comp Primrec.fst
    (tablePrimitive.comp (Primrec.fst.comp Primrec.snd))

theorem keepPrimitive : Primrec₂ keepCode := by
  have hg : Primrec₂ (fun (q : Nat × List PreparedPacketCode) (c : PreparedPacketCode) =>
      bif (tableOf c.1).all (fun op => decide (op.2.1 < q.1)) then some c else none) :=
    Primrec.cond (keepPredicatePrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact (Primrec.listFilterMap Primrec.snd hg).of_eq
    (fun q => filterAsMap (fun c => (tableOf c.1).all (fun op => decide (op.2.1 < q.1))) q.2)

theorem lowerFamilyPrimitive :
    Primrec (fun x : Nat × Nat × List PreparedPacketCode => lowerFamilyCode x.1 x.2.1 x.2.2) :=
  Primrec.listFilterMap (keepPrimitive.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (decodeRoutePrimitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem residualEffectivity : ResidualEffectivity :=
  ⟨decodePrimitive,decodeRoutePrimitive,keepPrimitive,lowerFamilyPrimitive⟩

#print axioms residualEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
