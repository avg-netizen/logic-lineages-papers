module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Proof
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open CircuitLinear
open LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)

attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem list1_pr {α β : Type} [Primcodable α] [Primcodable β]
    {a : α → β} (ha : Primrec a) : Primrec (fun x => [a x]) :=
  Primrec.list_cons.comp ha (Primrec.const [])
private theorem list2_pr {α β : Type} [Primcodable α] [Primcodable β]
    {a b : α → β} (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => [a x,b x]) :=
  Primrec.list_cons.comp ha (list1_pr hb)
private theorem list3_pr {α β : Type} [Primcodable α] [Primcodable β]
    {a b c : α → β} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun x => [a x,b x,c x]) :=
  Primrec.list_cons.comp ha (list2_pr hb hc)
private theorem list4_pr {α β : Type} [Primcodable α] [Primcodable β]
    {a b c d : α → β} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) : Primrec (fun x => [a x,b x,c x,d x]) :=
  Primrec.list_cons.comp ha (list3_pr hb hc hd)
private theorem list6_pr {α β : Type} [Primcodable α] [Primcodable β]
    {a b c d e f : α → β} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (he : Primrec e) (hf : Primrec f) :
    Primrec (fun x => [a x,b x,c x,d x,e x,f x]) :=
  Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (list4_pr hc hd he hf))

private theorem constant_pr {α : Type} [Primcodable α]
    {c : α → Int} {p : α → Nat} (hc : Primrec c) (hp : Primrec p) :
    Primrec (fun x => constant (c x) (p x)) :=
  hc.pair (hp.pair (Primrec.const none))

private theorem wire_pr {α : Type} [Primcodable α]
    {c : α → Int} {p i : α → Nat} (hc : Primrec c) (hp : Primrec p) (hi : Primrec i) :
    Primrec (fun x => wireMonomial (c x) (p x) (i x)) :=
  hc.pair (hp.pair (Primrec.option_some.comp hi))

private theorem scalarCount_pr {α : Type} [Primcodable α]
    {n g : α → Nat} (hn : Primrec n) (hg : Primrec g) :
    Primrec (fun x => scalarCount (n x) (g x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hn hg) hn)
    (Primrec.nat_mul.comp (Primrec.const 4) hg)

private theorem constantAux_pr {α : Type} [Primcodable α]
    {n g : α → Nat} (hn : Primrec n) (hg : Primrec g) :
    Primrec (fun x => constantAux (n x) (g x)) :=
  Primrec.nat_add.comp (scalarCount_pr hn hg) (Primrec.nat_mul.comp (Primrec.const 12) hg)

private theorem unknownCount_pr {α : Type} [Primcodable α]
    {n g : α → Nat} (hn : Primrec n) (hg : Primrec g) :
    Primrec (fun x => unknownCount (n x) (g x)) :=
  Primrec.nat_add.comp (constantAux_pr hn hg) (Primrec.const 9)

private theorem squareRows_pr {α : Type} [Primcodable α]
    {u v a : α → Nat} (hu : Primrec u) (hv : Primrec v) (ha : Primrec a) :
    Primrec (fun x => squareRows (u x) (v x) (a x)) := by
  have hwire (c : Int) (p k : Nat) :
      Primrec (fun x => wireMonomial c p (a x+k)) :=
    wire_pr (Primrec.const c) (Primrec.const p) (Primrec.nat_add.comp ha (Primrec.const k))
  exact list3_pr
    (list4_pr (hwire 1 1 0) (hwire (-1) 0 0) (hwire (-1) 0 3) (Primrec.const (constant 1)))
    (list4_pr (hwire 1 1 1) (hwire (-1) 0 1) (hwire (-1) 0 0)
      (wire_pr (Primrec.const 1) (Primrec.const 0) hu))
    (list4_pr (hwire 1 1 2) (hwire (-1) 0 2) (hwire (-1) 0 1)
      (wire_pr (Primrec.const 1) (Primrec.const 0) hv))

private theorem constantRows_pr {α : Type} [Primcodable α]
    {n a : α → Nat} (hn : Primrec n) (ha : Primrec a) :
    Primrec (fun x => constantRows (n x) (a x)) := by
  have hw (c : Int) (p k : Nat) :
      Primrec (fun x => wireMonomial c p (a x+k)) :=
    wire_pr (Primrec.const c) (Primrec.const p) (Primrec.nat_add.comp ha (Primrec.const k))
  have hsum : Primrec (fun x => (List.range (n x)).map (wireMonomial 1 0)) :=
    Primrec.list_map (Primrec.list_range.comp hn)
      (wire_pr (Primrec.const 1) (Primrec.const 0) Primrec.snd).to₂
  exact list6_pr
    (list4_pr (hw 1 1 2) (hw (-1) 0 2) (hw (-1) 0 5) (Primrec.const (constant 1)))
    (list4_pr (hw 1 2 3) (hw (-1) 0 3) (hw (-1) 0 6) (Primrec.const (constant 1)))
    (list4_pr (hw 1 1 4) (hw (-1) 0 4) (hw (-1) 0 3) (hw 1 0 2))
    (list4_pr (hw 1 1 7) (hw (-2) 0 7) (hw (-1) 0 2) (hw 1 0 0))
    (list4_pr (hw 1 2 8) (hw (-2) 0 8) (hw (-1) 0 3) (hw 1 0 0))
    (Primrec.list_append.comp hsum (list2_pr (hw 1 0 1) (hw (-1) 0 0)))

private theorem inputRows_pr {α : Type} [Primcodable α]
    {n g : α → Nat} (hn : Primrec n) (hg : Primrec g) :
    Primrec (fun x => inputRows (n x) (g x)) :=
  Primrec.list_map (Primrec.list_range.comp hn)
    (list3_pr (wire_pr (Primrec.const 1) (Primrec.const 0) Primrec.snd)
      (wire_pr (Primrec.const (-1)) (Primrec.const 0)
        (Primrec.nat_add.comp ((Primrec.nat_add.comp hn hg).comp Primrec.fst) Primrec.snd))
      (Primrec.const (constant (-1)))).to₂

private theorem gateRecordRows_pr {α : Type} [Primcodable α]
    {n g i tag u v : α → Nat} (hn : Primrec n) (hg : Primrec g) (hi : Primrec i)
    (ht : Primrec tag) (hu : Primrec u) (hv : Primrec v) :
    Primrec (fun x => gateRecordRows (n x) (g x) (i x) (tag x) (u x) (v x)) := by
  have hout : Primrec (fun x => wireMonomial 1 0 (n x+i x)) :=
    wire_pr (Primrec.const 1) (Primrec.const 0) (Primrec.nat_add.comp hn hi)
  have hcoef : Primrec (fun x => -((u x+1 : Nat) : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp (Primrec.nat_add.comp hu (Primrec.const 1)))
  have hconst : Primrec (fun x => gateRows (n x) (g x) (i x) (.constant (u x))) :=
    list1_pr (list2_pr hout (constant_pr hcoef (Primrec.const 0)))
  have hsum : Primrec (fun x => gateRows (n x) (g x) (i x) (.add (u x) (v x))) :=
    list1_pr (list3_pr hout (wire_pr (Primrec.const (-1)) (Primrec.const 0) hu)
      (wire_pr (Primrec.const (-1)) (Primrec.const 0) hv))
  let s : α → Nat := fun x => (n x+g x)+n x+4*i x
  let a : α → Nat := fun x => polynomialAux (n x) (g x)+12*i x
  have hs : Primrec s :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hn hg) hn)
      (Primrec.nat_mul.comp (Primrec.const 4) hi)
  have ha : Primrec a :=
    Primrec.nat_add.comp (scalarCount_pr hn hg) (Primrec.nat_mul.comp (Primrec.const 12) hi)
  have hsadd (k : Nat) : Primrec (fun x => s x+k) :=
    Primrec.nat_add.comp hs (Primrec.const k)
  have haadd (k : Nat) : Primrec (fun x => a x+k) :=
    Primrec.nat_add.comp ha (Primrec.const k)
  have hm : Primrec (fun x => gateRows (n x) (g x) (i x) (.mul (u x) (v x))) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (list2_pr
            (list3_pr (wire_pr (Primrec.const 1) (Primrec.const 0) hs)
              (wire_pr (Primrec.const (-1)) (Primrec.const 0) hu)
              (wire_pr (Primrec.const (-1)) (Primrec.const 0) hv))
            (list4_pr (wire_pr (Primrec.const 1) (Primrec.const 0) (hsadd 3))
              (wire_pr (Primrec.const (-1)) (Primrec.const 0) (hsadd 1))
              (wire_pr (Primrec.const (-1)) (Primrec.const 0) (hsadd 2))
              (wire_pr (Primrec.const (-1)) (Primrec.const 0) (Primrec.nat_add.comp hn hi))))
          (squareRows_pr hu (hsadd 1) ha))
        (squareRows_pr hv (hsadd 2) (haadd 4)))
      (squareRows_pr hs (hsadd 3) (haadd 8))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) hconst
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hsum hm)

private theorem gateCodeRows_pr {α : Type} [Primcodable α]
    {n g start : α → Nat} {code : α → List Nat} (hn : Primrec n) (hg : Primrec g)
    (hs : Primrec start) (hc : Primrec code) :
    Primrec (fun x => gateCodeRows (n x) (g x) (start x) (code x)) := by
  have hlen : Primrec (fun x => (code x).length / 3) :=
    Primrec.nat_div.comp (Primrec.list_length.comp hc) (Primrec.const 3)
  have hcell (k : Nat) : Primrec (fun p : α × Nat => (code p.1).getD (3*p.2+k) 0) :=
    (Primrec.list_getD 0).comp (hc.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) (Primrec.const k))
  exact Primrec.list_flatMap (Primrec.list_range.comp hlen)
    (gateRecordRows_pr (hn.comp Primrec.fst) (hg.comp Primrec.fst)
      (Primrec.nat_add.comp (hs.comp Primrec.fst) Primrec.snd)
      (hcell 0) (hcell 1) (hcell 2)).to₂

theorem systemCodePrimitive : Targets.SystemCodePrimitive := by
  have hfield (k : Nat) : Primrec (fun code : List Nat => code.getD k 0) :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const k)
  have hgate : Primrec (fun code : List Nat => code.drop 3) :=
    Primrec.list_drop.comp (Primrec.const 3) Primrec.id
  have hcount : Primrec (fun code : List Nat => (code.drop 3).length / 3) :=
    Primrec.nat_div.comp (Primrec.list_length.comp hgate) (Primrec.const 3)
  have houtput : Primrec (fun code : List Nat =>
      [[wireMonomial 1 0 (code.getD 1 0), wireMonomial (-1) 0 (code.getD 2 0)]]) :=
    list1_pr (list2_pr (wire_pr (Primrec.const 1) (Primrec.const 0) (hfield 1))
      (wire_pr (Primrec.const (-1)) (Primrec.const 0) (hfield 2)))
  exact (unknownCount_pr (hfield 0) hcount).pair
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp (inputRows_pr (hfield 0) hcount)
          (gateCodeRows_pr (hfield 0) hcount (Primrec.const 0) hgate)) houtput)
      (constantRows_pr (scalarCount_pr (hfield 0) hcount) (constantAux_pr (hfield 0) hcount)))

theorem encoderPrimitive : Targets.EncoderPrimitive :=
  Primrec.option_some.comp (Primrec.encode.comp systemCodePrimitive)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Proof
