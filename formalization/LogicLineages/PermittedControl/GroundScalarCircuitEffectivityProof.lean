module
public import LogicLineages.PermittedControl.GroundScalarCircuitCodeTargets
import Mathlib.Computability.Primrec.List

public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (RawGate emptyExpression)
open NaturalAffineGateGraph (Expression)
open OriginalPrintedRawFamilyFrontend (Args)

attribute [local irreducible] Nat.sqrt Nat.unpair

private def children (n : Nat) : List Nat :=
  if n % 4 = 2 then [(n / 4).unpair.1,(n / 4).unpair.2]
  else if n % 4 = 3 then [(n / 4).unpair.2] else []

private def assemble (n : Nat) (values : List (List RawGate)) : List RawGate :=
  if n % 4 = 0 then [leafGate (1,[])]
  else if n % 4 = 1 then [leafGate (1,[(1,inputName (n / 4))])]
  else if n % 4 = 2 then
    values.getD 0 [] ++ (values.getD 1 []).map (renameGate (values.getD 0 []).length) ++
      [addGate (values.getD 0 []).length (values.getD 1 []).length]
  else values.getD 0 [] ++ [shiftGate (n / 4).unpair.1 (values.getD 0 []).length]

private theorem children_lt (n c : Nat) (h : c ∈ children n) : c < n := by
  unfold children at h
  have hl := Nat.unpair_left_le (n / 4)
  have hr := Nat.unpair_right_le (n / 4)
  split_ifs at h with h2 h3
  · have hd : n / 4 < n := Nat.div_lt_self (by omega) (by decide)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> omega
  · have hd : n / 4 < n := Nat.div_lt_self (by omega) (by decide)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    subst h
    omega
  · simp at h

private theorem relCode_equation (n : Nat) : relCode n = assemble n ((children n).map relCode) := by
  conv_lhs => rw [relCode]
  unfold assemble children
  by_cases h0 : n % 4 = 0
  · simp [h0]
  by_cases h1 : n % 4 = 1
  · simp [h1]
  by_cases h2 : n % 4 = 2
  · simp [h0,h1,h2]
  · have h3 : n % 4 = 3 := by omega
    simp [h0,h1,h2,h3]

private theorem nodePrimitive : Primrec nodeName :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)

private theorem inputPrimitive : Primrec inputName :=
  Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

private theorem renameNamePrimitive : Primrec₂ renameName :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1))
    (Primrec.nat_add.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) Primrec.snd

private theorem renameGatePrimitive : Primrec₂ renameGate := by
  let A := Nat × RawGate
  have k : Primrec (fun q : A => q.1) := Primrec.fst
  have g1 : Primrec (fun q : A => q.2.1) := Primrec.fst.comp Primrec.snd
  have g2 : Primrec (fun q : A => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have g3 : Primrec (fun q : A => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have g4 : Primrec (fun q : A => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have e : Primrec (fun q : A => q.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have e1 : Primrec (fun q : A => q.2.2.2.2.2.1) := Primrec.fst.comp e
  have e2 : Primrec (fun q : A => q.2.2.2.2.2.2) := Primrec.snd.comp e
  have item : Primrec₂ (fun (q : A) (t : Int × Nat) => (t.1,renameName q.1 t.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (renameNamePrimitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have terms : Primrec (fun q : A => q.2.2.2.2.2.2.map (fun t => (t.1,renameName q.1 t.2))) :=
    Primrec.list_map e2 item
  have h := g1.pair ((renameNamePrimitive.comp k g2).pair ((renameNamePrimitive.comp k g3).pair
    (g4.pair (e1.pair terms))))
  exact h

private theorem leafOnePrimitive : Primrec (fun _ : Nat => leafGate (1,[])) := Primrec.const _

private theorem leafVarPrimitive : Primrec (fun n : Nat => leafGate (1,[(1,inputName (n / 4))])) := by
  have name : Primrec (fun n : Nat => inputName (n / 4)) :=
    inputPrimitive.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 4))
  have terms : Primrec (fun n : Nat => ([((1 : Int),inputName (n / 4))] : List (Int × Nat))) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair name) (Primrec.const [])
  have expr : Primrec (fun n : Nat => (((1 : Int),[((1 : Int),inputName (n / 4))]) : Expression)) :=
    (Primrec.const (1 : Int)).pair terms
  have h := (Primrec.const (0 : Nat)).pair ((Primrec.const (0 : Nat)).pair ((Primrec.const (nodeName 0)).pair
    ((Primrec.const ((0 : Nat),(0 : Nat))).pair expr)))
  exact h

private theorem addGatePrimitive : Primrec₂ addGate := by
  let A := Nat × Nat
  have la : Primrec (fun q : A => q.1) := Primrec.fst
  have lb : Primrec (fun q : A => q.2) := Primrec.snd
  have out : Primrec (fun q : A => nodeName (q.1 + q.2)) := nodePrimitive.comp (Primrec.nat_add.comp la lb)
  have left : Primrec (fun q : A => nodeName (q.1 - 1)) :=
    nodePrimitive.comp (Primrec.nat_sub.comp la (Primrec.const 1))
  have right : Primrec (fun q : A => nodeName (q.1 + q.2 - 1)) :=
    nodePrimitive.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp la lb) (Primrec.const 1))
  have terms : Primrec (fun q : A =>
      ([((1 : Int),nodeName (q.1 - 1)),((1 : Int),nodeName (q.1 + q.2 - 1))] : List (Int × Nat))) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair left)
      (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair right) (Primrec.const []))
  have h := (Primrec.const (0 : Nat)).pair ((Primrec.const (0 : Nat)).pair (out.pair
    ((Primrec.const ((0 : Nat),(0 : Nat))).pair ((Primrec.const (0 : Int)).pair terms))))
  exact h

private theorem shiftGatePrimitive : Primrec₂ shiftGate := by
  let A := Nat × Nat
  have hd : Primrec (fun q : A => q.1) := Primrec.fst
  have la : Primrec (fun q : A => q.2) := Primrec.snd
  have src : Primrec (fun q : A => nodeName (q.2 - 1)) :=
    nodePrimitive.comp (Primrec.nat_sub.comp la (Primrec.const 1))
  have out : Primrec (fun q : A => nodeName q.2) := nodePrimitive.comp la
  have h := (Primrec.const (1 : Nat)).pair (src.pair (out.pair ((hd.pair (Primrec.const (0 : Nat))).pair
    (Primrec.const emptyExpression))))
  exact h

private theorem childrenPrimitive : Primrec children := by
  have tag : Primrec (fun n : Nat => n % 4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  have q : Primrec (fun n : Nat => (n / 4).unpair) :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 4))
  have p1 : Primrec (fun n : Nat => (n / 4).unpair.1) := Primrec.fst.comp q
  have p2 : Primrec (fun n : Nat => (n / 4).unpair.2) := Primrec.snd.comp q
  have h := Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (Primrec.list_cons.comp p1 (Primrec.list_cons.comp p2 (Primrec.const [])))
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 3)) (Primrec.list_cons.comp p2 (Primrec.const []))
      (Primrec.const []))
  exact h

private theorem assemblePrimitive :
    Primrec (fun p : Nat × List (List RawGate) => assemble p.1 p.2) := by
  let A := Nat × List (List RawGate)
  have n : Primrec (fun p : A => p.1) := Primrec.fst
  have tag : Primrec (fun p : A => p.1 % 4) := Primrec.nat_mod.comp n (Primrec.const 4)
  have v0 : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List RawGate)).comp Primrec.snd (Primrec.const 0)
  have v1 : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List RawGate)).comp Primrec.snd (Primrec.const 1)
  have l0 : Primrec (fun p : A => (p.2.getD 0 []).length) := Primrec.list_length.comp v0
  have l1 : Primrec (fun p : A => (p.2.getD 1 []).length) := Primrec.list_length.comp v1
  have renamed : Primrec (fun p : A => (p.2.getD 1 []).map (renameGate (p.2.getD 0 []).length)) :=
    Primrec.list_map v1 (renameGatePrimitive.comp (l0.comp Primrec.fst) Primrec.snd)
  have addCase : Primrec (fun p : A => p.2.getD 0 [] ++ (p.2.getD 1 []).map (renameGate (p.2.getD 0 []).length) ++
      [addGate (p.2.getD 0 []).length (p.2.getD 1 []).length]) :=
    Primrec.list_append.comp (Primrec.list_append.comp v0 renamed)
      (Primrec.list_cons.comp (addGatePrimitive.comp l0 l1) (Primrec.const []))
  have head : Primrec (fun p : A => (p.1 / 4).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_div.comp n (Primrec.const 4)))
  have shiftCase : Primrec (fun p : A => p.2.getD 0 [] ++ [shiftGate (p.1 / 4).unpair.1 (p.2.getD 0 []).length]) :=
    Primrec.list_append.comp v0 (Primrec.list_cons.comp (shiftGatePrimitive.comp head l0) (Primrec.const []))
  have varCase : Primrec (fun p : A => [leafGate (1,[(1,inputName (p.1 / 4))])]) :=
    Primrec.list_cons.comp (leafVarPrimitive.comp n) (Primrec.const [])
  have h := Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (Primrec.const [leafGate (1,[])])
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) varCase
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) addCase shiftCase))
  exact h

private def step (_ : Unit) (values : List (List RawGate)) : Option (List RawGate) :=
  some (assemble values.length ((children values.length).map (fun i => values.getD i [])))

private theorem stepPrimitive : Primrec₂ step := by
  let A := Unit × List (List RawGate)
  have len : Primrec (fun p : A => p.2.length) := Primrec.list_length.comp Primrec.snd
  have look : Primrec₂ (fun (p : A) (i : Nat) => p.2.getD i []) :=
    (Primrec.list_getD ([] : List RawGate)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have vals : Primrec (fun p : A => (children p.2.length).map (fun i => p.2.getD i [])) :=
    Primrec.list_map (childrenPrimitive.comp len) look
  have h := Primrec.option_some.comp (assemblePrimitive.comp (len.pair vals))
  exact h

theorem relCodePrimitive : Primrec relCode := by
  have h : Primrec₂ (fun (_ : Unit) (n : Nat) => relCode n) := by
    apply Primrec.nat_strong_rec _ stepPrimitive
    intro a n
    unfold step
    simp only [List.length_map,List.length_range]
    apply congrArg some
    rw [relCode_equation n]
    apply congrArg (assemble n)
    apply List.map_congr_left
    intro i hi
    have hlt := children_lt n i hi
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

private theorem strictRowPrimitive : Primrec₂ strictRowCode := by
  let A := Nat × Nat
  have data : Primrec (fun q : A => (((0 : Nat),(0 : Nat),((-1 : Int),
      [((1 : Int),((0 : Nat),q.2,(0 : Int),(0 : Int))),((-1 : Int),((0 : Nat),q.1,(0 : Int),(0 : Int)))])) :
        NormalForm.Code.AtomData)) :=
    (Primrec.const _).pair ((Primrec.const _).pair ((Primrec.const _).pair
      (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair (Primrec.snd.pair (Primrec.const _))))
        (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair (Primrec.fst.pair (Primrec.const _))))
          (Primrec.const [])))))
  have h := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp data))
    (Primrec.const 2)
  exact h

private theorem weakRowPrimitive : Primrec₂ weakRowCode := by
  let A := Nat × Nat
  have data : Primrec (fun q : A => (((0 : Nat),(0 : Nat),((0 : Int),
      [((1 : Int),((0 : Nat),q.2,(0 : Int),(0 : Int))),((-1 : Int),((0 : Nat),q.1,(0 : Int),(0 : Int)))])) :
        NormalForm.Code.AtomData)) :=
    (Primrec.const _).pair ((Primrec.const _).pair ((Primrec.const _).pair
      (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair (Primrec.snd.pair (Primrec.const _))))
        (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair (Primrec.fst.pair (Primrec.const _))))
          (Primrec.const [])))))
  have h := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp data))
    (Primrec.const 2)
  exact h

private theorem counterPrimitive : Primrec (fun x : Nat × Nat × Nat => counterCode x.1 x.2.1 x.2.2) := by
  let X := Nat × Nat × Nat
  have tag : Primrec (fun x : X => x.1) := Primrec.fst
  have a : Primrec (fun x : X => x.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have sba : Primrec (fun x : X => strictRowCode x.2.2 x.2.1) := strictRowPrimitive.comp b a
  have sab : Primrec (fun x : X => strictRowCode x.2.1 x.2.2) := strictRowPrimitive.comp a b
  have wba : Primrec (fun x : X => weakRowCode x.2.2 x.2.1) := weakRowPrimitive.comp b a
  have dis : Primrec (fun x : X => 6 * Nat.pair (strictRowCode x.2.1 x.2.2) (strictRowCode x.2.2 x.2.1) + 5) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp sab sba))
      (Primrec.const 5)
  have h := Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) sba
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) wba dis)
  exact h

theorem queryCodeEffectivity : QueryCodeEffectivity := by
  let X := Nat × Nat × Nat
  have tag : Primrec (fun x : X => x.1) := Primrec.fst
  have a : Primrec (fun x : X => x.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have ra : Primrec (fun x : X => relCode x.2.1) := relCodePrimitive.comp a
  have rb : Primrec (fun x : X => relCode x.2.2) := relCodePrimitive.comp b
  have la : Primrec (fun x : X => (relCode x.2.1).length) := Primrec.list_length.comp ra
  have lb : Primrec (fun x : X => (relCode x.2.2).length) := Primrec.list_length.comp rb
  have known : Primrec (fun x : X => (List.range (x.2.1 + x.2.2 + 1)).map inputName) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.nat_add.comp a b)))
      (inputPrimitive.comp Primrec.snd).to₂
  have lo : Primrec (fun x : X => nodeName ((relCode x.2.1).length - 1)) :=
    nodePrimitive.comp (Primrec.nat_sub.comp la (Primrec.const 1))
  have hi : Primrec (fun x : X => nodeName ((relCode x.2.1).length + (relCode x.2.2).length - 1)) :=
    nodePrimitive.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp la lb) (Primrec.const 1))
  have matrix : Primrec (fun x : X => counterCode x.1 (nodeName ((relCode x.2.1).length - 1))
      (nodeName ((relCode x.2.1).length + (relCode x.2.2).length - 1))) := by
    have h := counterPrimitive.comp (tag.pair (lo.pair hi))
    exact h
  have gates : Primrec (fun x : X => relCode x.2.1 ++ (relCode x.2.2).map (renameGate (relCode x.2.1).length)) :=
    Primrec.list_append.comp ra (Primrec.list_map rb (renameGatePrimitive.comp (la.comp Primrec.fst) Primrec.snd))
  have h := (known.pair (matrix.pair gates)).pair (Primrec.const true)
  exact h

#print axioms relCodePrimitive
#print axioms queryCodeEffectivity

end LogicLineages.PermittedControl.GroundScalarCircuit
