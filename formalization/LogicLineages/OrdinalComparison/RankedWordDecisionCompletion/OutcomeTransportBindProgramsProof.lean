module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeRecursionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportPrograms
open OutcomeTransport
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem unary_primitive (tag : Nat) : Primrec (fun a : Nat => 6 * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const tag)

private def bindChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private theorem bindChildren_decreasing : ∀ code child, child ∈ bindChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [bindChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold bindChildren at h
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
private theorem bindChildren_primitive : Primrec bindChildren :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private def bindAssemble {α : Type*} (op : α → Nat → Nat) (args : α)
    (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then op args (code / 6)
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6

private theorem bind_equation {α : Type*} (op : α → Nat → Nat) (args : α) (code : Nat) :
    Code.bind (op args) code =
      bindAssemble op args code ((bindChildren code).map (Code.bind (op args))) := by
  rw [Code.bind]
  split_ifs <;> simp_all [bindChildren, bindAssemble]

private theorem bindAssemble_primitive {α : Type*} [Primcodable α]
    {op : α → Nat → Nat} (hop : Primrec₂ op) :
    Primrec (fun p : α × (Nat × List Nat) => bindAssemble op p.1 p.2.1 p.2.2) := by
  let A := α × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  have hatom : Primrec (fun p : A => op p.1 (p.2.1 / 6)) :=
    hop.comp Primrec.fst (quotient_primitive.comp hc)
  have hb : Primrec (fun p : A =>
      6 * Nat.pair (p.2.2.getD 0 0) (p.2.2.getD 1 0) + p.2.1 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1))
      (tag_primitive.comp hc)
  exact Primrec.ite ((tag_is 0).comp hc) (Primrec.const 0)
    (Primrec.ite ((tag_is 1).comp hc) (Primrec.const 1)
      (Primrec.ite ((tag_is 2).comp hc) hatom
        (Primrec.ite ((tag_is 3).comp hc) ((unary_primitive 3).comp h0) hb)))

private def bindStep {α : Type*} (op : α → Nat → Nat) (args : α)
    (values : List Nat) : Option Nat :=
  some (bindAssemble op args values.length
    ((bindChildren values.length).map (fun i => values.getD i 0)))

private theorem bindStep_primitive {α : Type*} [Primcodable α]
    {op : α → Nat → Nat} (hop : Primrec₂ op) : Primrec₂ (bindStep op) := by
  let A := α × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (bindChildren p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map
      (bindChildren_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (bindChildren p.2.length).map (fun i => p.2.getD i 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp ((bindAssemble_primitive hop).comp hp)

/-- Uniform complete-formula substitution on every numerical input. Unlike
an atom-payload map, this operation can replace a sign test by true or false. -/
theorem bind_primitive {α : Type*} [Primcodable α] {op : α → Nat → Nat}
    (hop : Primrec₂ op) : Primrec₂ (fun args code => Code.bind (op args) code) := by
  apply Primrec.nat_strong_rec _ (bindStep_primitive hop)
  intro args code
  unfold bindStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [bind_equation op args code]
  apply congrArg (bindAssemble op args code)
  apply List.map_congr_left
  intro i hi
  have hlt := bindChildren_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

#print axioms unary_primitive
#print axioms bindChildren_decreasing
#print axioms tag_primitive
#print axioms quotient_primitive
#print axioms tag_is
#print axioms left_primitive
#print axioms right_primitive
#print axioms bindChildren_primitive
#print axioms bind_equation
#print axioms bindAssemble_primitive
#print axioms bindStep_primitive
#print axioms bind_primitive

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportPrograms
