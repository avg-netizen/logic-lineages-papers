module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramInterfacesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Proof

/-- A typed finite basis has exactly the same ordered zip semantics as its
literal list representation. Repeated/dependent entries are not quotiented. -/
theorem zipOfFn {A B D:Type} {k:Nat} (f:Fin k→A) (g:Fin k→B) (h:A→B→D):
    (List.ofFn f).zipWith h (List.ofFn g)=List.ofFn (fun j=>h (f j) (g j)):=by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Explicit Nat operand type avoids treating a list coercion as a new input
assignment; both forms of the original signed affine sum are identical. -/
theorem zipNatCast (rs:List Int) (bs:List Nat):
    rs.zipWith (fun r b=>r*(b:Int)) bs=
      rs.zipWith (fun (r:Int) (b:Nat)=>r*(b:Int)) bs:=by
  induction rs generalizing bs with
  | nil=>rfl
  | cons r rs ih=>
    cases bs with
    | nil=>rfl
    | cons b bs=>
      change r*(b:Int)::(rs.zipWith (fun r b=>r*(b:Int)) bs)=
        r*(b:Int)::(rs.zipWith (fun (r:Int) (b:Nat)=>r*(b:Int)) bs)
      rw [ih]

theorem castSumOfFn (k:Nat):∀f:Fin k→Nat,
    ((List.ofFn f).sum:Int)=(List.ofFn (fun j=>(f j:Int))).sum:=by
  induction k with
  | zero=>intro f;rfl
  | succ k ih=>
    intro f
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [List.sum_cons,Nat.cast_add,ih]

theorem subSumOfFn (k:Nat):∀f g:Fin k→Int,
    (List.ofFn (fun j=>f j-g j)).sum=(List.ofFn f).sum-(List.ofFn g).sum:=by
  induction k with
  | zero=>intro f g;rfl
  | succ k ih=>
    intro f g
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp only [List.sum_cons,ih]
    ring

theorem atomShape (k:Nat) (Γ:List Nat) (C:Certificate (k::Γ)) (ν:Nat→Nat) (a:Atom k):
    (asAtom a).coefficients.length=(basisValues k Γ C ν).length∧
      ∀c∈(asAtom a).coefficients,1≤c:=by
  constructor
  · simp [asAtom,basisValues]
  · intro c hc
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hc
    omega

theorem rowWellFormed (k:Nat) (Γ:List Nat) (C:Certificate (k::Γ)) (E F:Upper k) (ν:Nat→Nat):
    BalancedRow.wellFormed (basisValues k Γ C ν) (comparisonRow E F):=by
  constructor
  · simp [comparisonRow,basisValues]
  · intro a ha
    rcases List.mem_append.mp ha with he|hf
    · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp he
      exact atomShape k Γ C ν b.2
    · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hf
      exact atomShape k Γ C ν b.2

theorem actualHeadValidity:Targets.ActualHeadValidity:=by
  intro k Γ E F hE hF a ha
  rcases List.mem_append.mp ha with he|hf
  · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp he
    exact hE b hb
  · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hf
    exact hF b hb

theorem outsideDifference {k:Nat} (a b v:Fin k→Nat):
    ((List.ofFn (fun j=>(a j:Int)-(b j:Int))).zipWith
      (fun (r:Int) (x:Nat)=>r*(x:Int)) (List.ofFn v)).sum=
      (((List.ofFn a).zipWith (fun (x y:Nat)=>(x*y:Nat)) (List.ofFn v)).sum:Int)-
      (((List.ofFn b).zipWith (fun (x y:Nat)=>(x*y:Nat)) (List.ofFn v)).sum:Int):=by
  rw [zipOfFn,zipOfFn,zipOfFn,castSumOfFn,castSumOfFn]
  have ht:(fun j:Fin k=>((a j:Int)-(b j:Int))*(v j:Int))=
      (fun j=>((a j*v j:Nat):Int)-((b j*v j:Nat):Int)):=by
    funext j
    simp only [Nat.cast_mul]
    ring
  simpa only [ht,subSumOfFn]

private theorem castSumMap {A:Type} (xs:List A) (f:A→Nat):
    ((xs.map f).sum:Int)=(xs.map (fun a=>(f a:Int))).sum:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]

private theorem negSumMap {A:Type} (xs:List A) (f:A→Int):
    (xs.map (fun a=> -(f a))).sum= -(xs.map f).sum:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.map_cons,List.sum_cons,ih,neg_add]

private theorem castHeadSum {k:Nat} (E:Upper k) (basis:List Nat):
    ((E.atoms.map (fun a=>(a.1+1)*actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)))).sum:Int)=
    (E.atoms.map (fun a=>(a.1+1:Int)*(actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)):Int))).sum:=by
  rw [castSumMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]

private theorem atom_head {k:Nat} (a:Atom k):(asAtom a).head=a.head:=rfl

theorem actualComparisonRow:Targets.ActualComparisonRow:=by
  intro k Γ C E F ν
  refine ⟨rowWellFormed k Γ C E F ν,?_⟩
  simp only [value,basisValues]
  unfold BalancedRow.value BalancedRow.remainderValue comparisonRow
  rw [zipNatCast,outsideDifference]
  simp only [List.map_append,List.map_map,List.sum_append,Function.comp_def,atom_head,neg_mul]
  rw [negSumMap]
  simp only [Nat.cast_add]
  rw [castHeadSum,castHeadSum]
  ring
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Proof
