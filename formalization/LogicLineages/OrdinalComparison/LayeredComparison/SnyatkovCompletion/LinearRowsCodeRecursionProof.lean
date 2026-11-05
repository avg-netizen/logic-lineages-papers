module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
open LinearRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem unary_primitive (tag : Nat) :
    Primrec (fun a : Nat => 6 * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
    (Primrec.const tag)

private def children (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private def mapAssemble {α : Type*} (op : α → Nat → Nat) (args : α)
    (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then 6 * op args (code / 6) + 2
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6

private theorem map_equation {α : Type*} (op : α → Nat → Nat) (args : α) (code : Nat) :
    Code.mapAtoms (op args) code =
      mapAssemble op args code ((children code).map (Code.mapAtoms (op args))) := by
  rw [Code.mapAtoms]
  split_ifs <;> simp_all [children, mapAssemble]

private theorem mapAssemble_primitive {α : Type*} [Primcodable α]
    {op : α → Nat → Nat} (hop : Primrec₂ op) :
    Primrec (fun p : α × (Nat × List Nat) => mapAssemble op p.1 p.2.1 p.2.2) := by
  let A := α × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  have hatom : Primrec (fun p : A => 6 * op p.1 (p.2.1 / 6) + 2) :=
    (unary_primitive 2).comp (hop.comp Primrec.fst (quotient_primitive.comp hc))
  have hb : Primrec (fun p : A =>
      6 * Nat.pair (p.2.2.getD 0 0) (p.2.2.getD 1 0) + p.2.1 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1))
      (tag_primitive.comp hc)
  exact Primrec.ite ((tag_is 0).comp hc) (Primrec.const 0)
    (Primrec.ite ((tag_is 1).comp hc) (Primrec.const 1)
      (Primrec.ite ((tag_is 2).comp hc) hatom
        (Primrec.ite ((tag_is 3).comp hc) ((unary_primitive 3).comp h0) hb)))

private def mapStep {α : Type*} (op : α → Nat → Nat) (args : α)
    (values : List Nat) : Option Nat :=
  some (mapAssemble op args values.length
    ((children values.length).map (fun i => values.getD i 0)))

private theorem mapStep_primitive {α : Type*} [Primcodable α]
    {op : α → Nat → Nat} (hop : Primrec₂ op) : Primrec₂ (mapStep op) := by
  let A := α × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (children p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map
      (children_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (children p.2.length).map (fun i => p.2.getD i 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp ((mapAssemble_primitive hop).comp hp)

/-- Uniform closure of the literal Boolean atom-map under primitive-recursive
payload transformations. The actual formula code remains the recursive input. -/
theorem mapAtoms_primitive {α : Type*} [Primcodable α] {op : α → Nat → Nat}
    (hop : Primrec₂ op) : Primrec₂ (fun args code => Code.mapAtoms (op args) code) := by
  apply Primrec.nat_strong_rec _ (mapStep_primitive hop)
  intro args code
  unfold mapStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [map_equation op args code]
  apply congrArg (mapAssemble op args code)
  apply List.map_congr_left
  intro i hi
  have hlt := children_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

private def atomsAssemble (code : Nat) (values : List (List Nat)) : List Nat :=
  if code % 6 = 0 then []
  else if code % 6 = 1 then []
  else if code % 6 = 2 then [code / 6]
  else if code % 6 = 3 then values.getD 0 []
  else values.getD 0 [] ++ values.getD 1 []

private theorem atoms_equation (code : Nat) :
    Code.atoms code = atomsAssemble code ((children code).map Code.atoms) := by
  rw [Code.atoms]
  split_ifs <;> simp_all [children, atomsAssemble]

private theorem atomsAssemble_primitive :
    Primrec (fun p : Nat × List (List Nat) => atomsAssemble p.1 p.2) := by
  have h0 : Primrec (fun p : Nat × List (List Nat) => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : Nat × List (List Nat) => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 1)
  have hatom : Primrec (fun p : Nat × List (List Nat) => [p.1 / 6]) :=
    Primrec.list_cons.comp (quotient_primitive.comp Primrec.fst) (Primrec.const [])
  exact Primrec.ite ((tag_is 0).comp Primrec.fst) (Primrec.const [])
    (Primrec.ite ((tag_is 1).comp Primrec.fst) (Primrec.const [])
      (Primrec.ite ((tag_is 2).comp Primrec.fst) hatom
        (Primrec.ite ((tag_is 3).comp Primrec.fst) h0 (Primrec.list_append.comp h0 h1))))

private def atomsStep (_ : Unit) (values : List (List Nat)) : Option (List Nat) :=
  some (atomsAssemble values.length
    ((children values.length).map (fun i => values.getD i [])))

private theorem atomsStep_primitive : Primrec₂ atomsStep := by
  let A := Unit × List (List Nat)
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 []) :=
    (Primrec.list_getD ([] : List Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (children p.2.length).map (fun i => p.2.getD i [])) :=
    Primrec.list_map
      (children_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.2.length, (children p.2.length).map (fun i => p.2.getD i []))) :=
    (Primrec.list_length.comp Primrec.snd).pair hm
  exact Primrec.option_some.comp (atomsAssemble_primitive.comp hp)

theorem atoms_primitive : Primrec Code.atoms := by
  have h : Primrec₂ (fun (_ : Unit) code => Code.atoms code) := by
    apply Primrec.nat_strong_rec _ atomsStep_primitive
    intro args code
    unfold atomsStep
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [atoms_equation code]
    apply congrArg (atomsAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := children_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
