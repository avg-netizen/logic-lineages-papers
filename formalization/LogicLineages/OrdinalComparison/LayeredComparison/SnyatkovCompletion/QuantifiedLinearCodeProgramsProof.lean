module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
attribute [local irreducible] Nat.sqrt Nat.unpair

private def children (code : Nat) : List Nat :=
  if code % 4 = 0 then []
  else if code % 4 = 1 then [code / 4]
  else if code % 4 = 2 then [(code / 4).unpair.1, (code / 4).unpair.2]
  else [(code / 4).unpair.2]

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 4 = 0
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 4)
  have hr := Nat.unpair_right_le (code / 4)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem tag_primitive : Primrec (fun code : Nat => code % 4) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 4) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 4)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 4 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 4).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 4).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem children_primitive : Primrec children :=
  Primrec.ite (tag_is 0) (Primrec.const [])
    (Primrec.ite (tag_is 1)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.ite (tag_is 2)
        (Primrec.list_cons.comp left_primitive
          (Primrec.list_cons.comp right_primitive (Primrec.const [])))
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private def recursionStep {α β : Type*} (default : β)
    (assemble : α → Nat → List β → β) (args : α) (values : List β) : Option β :=
  some (assemble args values.length
    ((children values.length).map (fun i => values.getD i default)))

private theorem recursionStep_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    (default : β) {assemble : α → Nat → List β → β}
    (ha : Primrec (fun p : α × (Nat × List β) => assemble p.1 p.2.1 p.2.2)) :
    Primrec₂ (recursionStep default assemble) := by
  let A := α × List β
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 default) :=
    (Primrec.list_getD default).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (children p.2.length).map (fun i => p.2.getD i default)) :=
    Primrec.list_map
      (children_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (children p.2.length).map (fun i => p.2.getD i default))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp (ha.comp hp)

private theorem recursion_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    (default : β) (f : α → Nat → β) (assemble : α → Nat → List β → β)
    (ha : Primrec (fun p : α × (Nat × List β) => assemble p.1 p.2.1 p.2.2))
    (he : ∀ args code, f args code = assemble args code ((children code).map (f args))) :
    Primrec₂ f := by
  apply Primrec.nat_strong_rec _ (recursionStep_primitive default ha)
  intro args code
  unfold recursionStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [he args code]
  apply congrArg (assemble args code)
  apply List.map_congr_left
  intro i hi
  have hlt := children_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

private def freeLinearAssemble (i code : Nat) (values : List Bool) : Bool :=
  if code % 4 = 0 then LinearRows.Code.isLinear i (code / 4)
  else if code % 4 = 1 then values.getD 0 false
  else if code % 4 = 2 then values.getD 0 false && values.getD 1 false
  else if i = (code / 4).unpair.1 then true else values.getD 0 false

private theorem freeLinear_equation (i code : Nat) :
    QuantifiedLinear.Code.freeLinear i code =
      freeLinearAssemble i code ((children code).map (QuantifiedLinear.Code.freeLinear i)) := by
  rw [QuantifiedLinear.Code.freeLinear]
  split_ifs <;> simp_all [children, freeLinearAssemble]

private theorem freeLinearAssemble_primitive :
    Primrec (fun p : Nat × (Nat × List Bool) => freeLinearAssemble p.1 p.2.1 p.2.2) := by
  let A := Nat × (Nat × List Bool)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 false) :=
    (Primrec.list_getD false).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 false) :=
    (Primrec.list_getD false).comp hv (Primrec.const 1)
  exact Primrec.ite ((tag_is 0).comp hc)
    (LinearRowsCodeProof.isLinear_primitive.comp Primrec.fst (quotient_primitive.comp hc))
    (Primrec.ite ((tag_is 1).comp hc) h0
      (Primrec.ite ((tag_is 2).comp hc) (Primrec.and.comp h0 h1)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (left_primitive.comp hc))
          (Primrec.const true) h0)))

theorem freeLinear_primitive : Primrec₂ QuantifiedLinear.Code.freeLinear :=
  recursion_primitive false _ _ freeLinearAssemble_primitive freeLinear_equation

private def admissibleAssemble (_ : Unit) (code : Nat) (values : List Bool) : Bool :=
  if code % 4 = 0 then true
  else if code % 4 = 1 then values.getD 0 false
  else if code % 4 = 2 then values.getD 0 false && values.getD 1 false
  else values.getD 0 false &&
    QuantifiedLinear.Code.freeLinear (code / 4).unpair.1 (code / 4).unpair.2

private theorem admissible_equation (args : Unit) (code : Nat) :
    QuantifiedLinear.Code.admissible code =
      admissibleAssemble args code ((children code).map QuantifiedLinear.Code.admissible) := by
  rw [QuantifiedLinear.Code.admissible]
  split_ifs <;> simp_all [children, admissibleAssemble]

private theorem admissibleAssemble_primitive :
    Primrec (fun p : Unit × (Nat × List Bool) => admissibleAssemble p.1 p.2.1 p.2.2) := by
  let A := Unit × (Nat × List Bool)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 false) :=
    (Primrec.list_getD false).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 false) :=
    (Primrec.list_getD false).comp hv (Primrec.const 1)
  exact Primrec.ite ((tag_is 0).comp hc) (Primrec.const true)
    (Primrec.ite ((tag_is 1).comp hc) h0
      (Primrec.ite ((tag_is 2).comp hc) (Primrec.and.comp h0 h1)
        (Primrec.and.comp h0
          (freeLinear_primitive.comp (left_primitive.comp hc) (right_primitive.comp hc)))))

theorem admissible_primitive : Primrec QuantifiedLinear.Code.admissible :=
  (recursion_primitive false (fun (_ : Unit) => QuantifiedLinear.Code.admissible) _
    admissibleAssemble_primitive admissible_equation).comp (Primrec.const ()) Primrec.id

private def eliminateAssemble (_ : Unit) (code : Nat) (values : List Nat) : Nat :=
  if code % 4 = 0 then code / 4
  else if code % 4 = 1 then 6 * values.getD 0 0 + 3
  else if code % 4 = 2 then 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + 4
  else LinearRows.Code.eliminate (code / 4).unpair.1 (values.getD 0 0)

private theorem eliminate_equation (args : Unit) (code : Nat) :
    QuantifiedLinear.Code.eliminate code =
      eliminateAssemble args code ((children code).map QuantifiedLinear.Code.eliminate) := by
  rw [QuantifiedLinear.Code.eliminate]
  split_ifs <;> simp_all [children, eliminateAssemble]

private theorem eliminateAssemble_primitive :
    Primrec (fun p : Unit × (Nat × List Nat) => eliminateAssemble p.1 p.2.1 p.2.2) := by
  let A := Unit × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  exact Primrec.ite ((tag_is 0).comp hc) (quotient_primitive.comp hc)
    (Primrec.ite ((tag_is 1).comp hc)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) h0) (Primrec.const 3))
      (Primrec.ite ((tag_is 2).comp hc)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1)) (Primrec.const 4))
        (LinearRowsCodeProof.eliminate_primitive.comp (left_primitive.comp hc) h0)))

theorem eliminate_primitive : Primrec QuantifiedLinear.Code.eliminate :=
  (recursion_primitive (0 : Nat) (fun (_ : Unit) => QuantifiedLinear.Code.eliminate) _
    eliminateAssemble_primitive eliminate_equation).comp (Primrec.const ()) Primrec.id

theorem actualNumericPrograms : QuantifiedLinearTargets.ActualNumericPrograms :=
  ⟨freeLinear_primitive, admissible_primitive, eliminate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearProof
