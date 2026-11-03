module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxRowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHeadProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBasisProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Proof

private theorem outsideSupport {k:Nat} {Γ:List Nat} (C:Certificate (k::Γ)) (E:Upper k)
    (j:Fin k) (hn:E.outside j≠0) {i:Nat} (hi:i∈rawVariables Γ C.1 (C.2 j)):
    i∈rawVariables (k::Γ) C E:=by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨j,by simp,?_⟩
  simpa only [if_neg hn] using hi

private theorem headSupport {k:Nat} {Γ:List Nat} (C:Certificate (k::Γ)) (E:Upper k)
    (a:Nat×Atom k) (ha:a∈E.atoms) (j:Fin k) {i:Nat} (hi:i∈rawVariables Γ C.1 (C.2 j)):
    i∈rawVariables (k::Γ) C E:=by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,?_⟩
  exact List.mem_flatMap.mpr ⟨j,by simp,hi⟩

theorem supportStability:Targets.ActualRawSupportStability:=by
  intro Γ
  induction Γ with
  | nil=>
    intro C E ν μ h
    exact BaseTermPrograms.Proof.supportStability E ν μ h
  | cons k Γ ih=>
    intro C E ν μ h
    cases hAtoms:E.atoms with
    | nil=>
      simp only [value,hAtoms,List.map_nil,List.sum_nil,Nat.add_zero]
      rw [zipOfFn,zipOfFn]
      apply congrArg (fun n=>E.constant+n)
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext j
      by_cases hj:E.outside j=0
      · simp only [hj,Nat.zero_mul]
      · rw [ih C.1 (C.2 j) ν μ (fun i hi=>h i (outsideSupport C E j hj hi))]
    | cons a atoms=>
      have ha:a∈E.atoms:=by rw [hAtoms];exact List.mem_cons_self
      have hb:(fun j:Fin k=>value Γ C.1 (C.2 j) ν)=
          (fun j:Fin k=>value Γ C.1 (C.2 j) μ):=by
        funext j
        exact ih C.1 (C.2 j) ν μ (fun i hi=>h i (headSupport C E a ha j hi))
      simp only [value]
      rw [hb]

private theorem sum_member {xs:List Nat} {x:Nat} (hx:x∈xs):x≤xs.sum:=by
  induction xs with
  | nil=>cases hx
  | cons a xs ih=>
    rcases List.mem_cons.mp hx with h|h
    · subst x;simp only [List.sum_cons];omega
    · have ht:=ih h;simp only [List.sum_cons];omega

private theorem outside_le_value {k:Nat} {Γ:List Nat} (C:Certificate (k::Γ)) (E:Upper k)
    (ν:Nat→Nat) (j:Fin k):
    E.outside j*value Γ C.1 (C.2 j) ν≤value (k::Γ) C E ν:=by
  have hm:E.outside j*value Γ C.1 (C.2 j) ν∈
      (List.ofFn E.outside).zipWith (·*·) (basisValues k Γ C ν):=by
    rw [basisValues,zipOfFn]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have hs:=sum_member hm
  simp only [value,basisValues] at hs ⊢
  omega

private theorem head_le_value {k:Nat} {Γ:List Nat} (C:Certificate (k::Γ)) (E:Upper k)
    (ν:Nat→Nat) (a:Nat×Atom k) (ha:a∈E.atoms):
    actualHeadValue a.2.head.1.repr (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2))≤
      value (k::Γ) C E ν:=by
  let head:=actualHeadValue a.2.head.1.repr (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2))
  have hm:(a.1+1)*head∈E.atoms.map (fun b=>(b.1+1)*actualHeadValue b.2.head.1.repr
      (BalancedRow.input (basisValues k Γ C ν) (asAtom b.2))):=List.mem_map.mpr ⟨a,ha,rfl⟩
  have hs:=sum_member hm
  have hcoef:head≤(a.1+1)*head:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right head (show 1≤a.1+1 by omega)
  simp only [head,basisValues] at hcoef hs
  simp only [value,basisValues]
  omega

theorem supportDomination:Targets.ActualRawSupportDomination:=by
  intro Γ
  induction Γ with
  | nil=>
    intro C hC E hE ν i hi
    exact BaseTermPrograms.Proof.supportDomination E ν i hi
  | cons k Γ ih=>
    intro C hC E hE ν i hi
    rcases List.mem_append.mp hi with hout|hhead
    · obtain ⟨j,hj,hv⟩:=List.mem_flatMap.mp hout
      have hn:E.outside j≠0:=by
        intro hz
        simp only [if_pos hz,List.not_mem_nil] at hv
      have hm:i∈rawVariables Γ C.1 (C.2 j):=by simpa only [if_neg hn] using hv
      have hb:=ih C.1 hC.1 (C.2 j) (hC.2 j) ν i hm
      have hc:1≤E.outside j:=by omega
      have hp:value Γ C.1 (C.2 j) ν≤E.outside j*value Γ C.1 (C.2 j) ν:=by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (value Γ C.1 (C.2 j) ν) hc
      exact (hb.trans hp).trans (outside_le_value C E ν j)
    · obtain ⟨a,ha,hv⟩:=List.mem_flatMap.mp hhead
      obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hv
      have hb:=ih C.1 hC.1 (C.2 j) (hC.2 j) ν i hm
      let zero:Upper k:=⟨0,(fun _=>0),[]⟩
      have hw:=rowWellFormed k Γ C E zero ν
      have ha':((a.1+1:Int),asAtom a.2)∈(comparisonRow E zero).atoms:=
        List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
      have hs:=(BalancedRow.Proof.basisBounds (basisValues k Γ C ν) (comparisonRow E zero)
        hw _ ha').1
      have hmem:value Γ C.1 (C.2 j) ν∈basisValues k Γ C ν:=List.mem_ofFn.mpr ⟨j,rfl⟩
      have hdom:actualOrdinalNorm a.2.head.1.repr≤ BalancedRow.input (basisValues k Γ C ν) (asAtom a.2):=by
        change actualOrdinalNorm a.2.head.1.repr≤
          actualOrdinalNorm a.2.head.1.repr+a.2.offset+
            ((List.ofFn (fun j=>a.2.factors j+1)).zipWith (·*·) (basisValues k Γ C ν)).sum
        omega
      have he:=HeterogeneousHead.Proof.inputExpansive a.2.head (hE a ha)
        (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2)) hdom
      exact (((hb.trans (sum_member hmem)).trans hs).trans he.le).trans (head_le_value C E ν a ha)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Proof
