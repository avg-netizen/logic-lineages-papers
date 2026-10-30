module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizerProgram
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCodeProof

@[expose] public section

/-! Genuine numerical effectivity of the literal compiler. Generic parser
closure hypotheses are instantiated with actual proved numeric row programs;
no such hypothesis remains in the final target. The lexer certificate below
reproduces the accepted enumeration proof's previously private supplier,
leaving its original source unchanged.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramEffectivity

open ExponentialNormalizerProgram FiniteComparisonEnumeration
open ExponentialHereditaryCodec ExponentialNormalFormCodeOperations
open ExponentialNormalFormProductCode ExponentialNormalFormCodec
open ExponentialNormalFormCodecProof ExponentialHereditaryCodecProof
open ExponentialNormalFormCodeOperationsEffectivity
  (pr_variableCode pr_addCode pr_canonicalEntries)

theorem pr_tokenize : Primrec tokenize := by
  let children : List Nat → List (List Nat) := fun xs =>
    if xs.length = 0 then [] else [xs.drop (if xs.head! = 1 then 2 else 1)]
  let assemble : List Nat → List (Option (List Token)) → Option (Option (List Token)) := fun xs rs =>
    some (if xs.length = 0 then some [] else
      if xs.head! = 0 then rs.head!.map ((0,0) :: ·) else
      if xs.head! = 1 then (if 2 ≤ xs.length then rs.head!.map ((1,xs.getD 1 0) :: ·) else none) else
      if xs.head! = 2 then rs.head!.map ((2,0) :: ·) else
      if xs.head! = 3 then rs.head!.map ((3,0) :: ·) else none)
  have hz : PrimrecPred (fun xs : List Nat => xs.length = 0) := Primrec.eq.comp Primrec.list_length (Primrec.const 0)
  have he (n : Nat) : PrimrecPred (fun xs : List Nat => xs.head! = n) := Primrec.eq.comp Primrec.list_headI (Primrec.const n)
  have hchildren : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.list_drop.comp (Primrec.ite (he 1) (Primrec.const 2) (Primrec.const 1)) Primrec.id) (Primrec.const []))
  have hm (tag : Nat) (payload : List Nat → Nat) (hp : Primrec payload) :
      Primrec (fun p : List Nat × List (Option (List Token)) => p.2.head!.map ((tag,payload p.1) :: ·)) := by
    apply Primrec.option_map (Primrec.list_headI.comp Primrec.snd)
    exact (Primrec.list_cons.comp ((Primrec.const tag).pair (hp.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to₂
  have ha : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite (hz.comp Primrec.fst) (Primrec.const (some []))
    apply Primrec.ite ((he 0).comp Primrec.fst) (hm 0 _ (Primrec.const 0))
    apply Primrec.ite ((he 1).comp Primrec.fst)
    · exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.fst))
        (hm 1 _ ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 1))) (Primrec.const none)
    · exact Primrec.ite ((he 2).comp Primrec.fst) (hm 2 _ (Primrec.const 0))
        (Primrec.ite ((he 3).comp Primrec.fst) (hm 3 _ (Primrec.const 0)) (Primrec.const none))
  apply Primrec.nat_omega_rec' tokenize Primrec.list_length hchildren ha
  · intro xs ys hy
    by_cases hz' : xs.length = 0
    · simp only [children,if_pos hz',List.not_mem_nil] at hy
    · simp only [children,if_neg hz',List.mem_singleton] at hy
      subst ys
      split <;> simp only [List.length_drop] <;> omega
  · intro xs
    cases xs with
    | nil => simp [children,assemble,tokenize]
    | cons tag rest =>
      rcases tag with _ | _ | _ | _ | tag
      · simp [children,assemble,tokenize]
      · cases rest <;> simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]


def singletonValue {α : Type} : List α → Option α
  | [x] => some x
  | _ => none

theorem pr_singletonValue {α : Type} [Primcodable α] : Primrec (@singletonValue α) := by
  have h : Primrec (fun xs : List α => if xs.length = 1 then xs[0]? else none) :=
    Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1))
      (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0)) (Primrec.const none)
  apply h.of_eq
  intro xs
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [singletonValue]

theorem pr_processStep {σ α : Type} [Primcodable σ] [Primcodable α]
    (d : σ → Nat) (one : σ → α) (variableValue : σ → Nat → α)
    (addition exponential : σ → α → α → α)
    (hd : Primrec d) (hone : Primrec one)
    (hvar : Primrec (fun p : σ × Nat => variableValue p.1 p.2))
    (hadd : Primrec (fun p : σ × α × α => addition p.1 p.2.1 p.2.2))
    (hexp : Primrec (fun p : σ × α × α => exponential p.1 p.2.1 p.2.2)) :
    Primrec (fun p : σ × Token × List α =>
      processStep (one p.1) (variableValue p.1) (addition p.1) (exponential p.1)
        (d p.1) p.2.1 p.2.2) := by
  let raw : σ × Token × List α → Option (List α) := fun p =>
    if p.2.1.1 = 0 then some (one p.1 :: p.2.2) else
    if p.2.1.1 = 1 then
      if p.2.1.2 < d p.1 then some (variableValue p.1 p.2.1.2 :: p.2.2) else none
    else if p.2.1.1 = 2 then
      if 2 ≤ p.2.2.length then some
        (addition p.1 (p.2.2.getD 0 (one p.1)) (p.2.2.getD 1 (one p.1)) :: p.2.2.drop 2)
      else none
    else if p.2.1.1 = 3 then
      if 2 ≤ p.2.2.length then some
        (exponential p.1 (p.2.2.getD 0 (one p.1)) (p.2.2.getD 1 (one p.1)) :: p.2.2.drop 2)
      else none
    else none
  have hp : Primrec (fun p : σ × Token × List α => p.1) := Primrec.fst
  have ht : Primrec (fun p : σ × Token × List α => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hi : Primrec (fun p : σ × Token × List α => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : σ × Token × List α => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hg (i : Nat) : Primrec (fun p : σ × Token × List α => p.2.2.getD i (one p.1)) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp hs (Primrec.const i)) (hone.comp hp)
  have hdrop := Primrec.list_drop.comp (Primrec.const 2) hs
  have hlen := Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp hs)
  have he (i : Nat) := Primrec.eq.comp ht (Primrec.const i)
  have hraw : Primrec raw := by
    apply Primrec.ite (he 0)
      (Primrec.option_some.comp (Primrec.list_cons.comp (hone.comp hp) hs))
    apply Primrec.ite (he 1)
      (Primrec.ite (Primrec.nat_lt.comp hi (hd.comp hp))
        (Primrec.option_some.comp (Primrec.list_cons.comp (hvar.comp (hp.pair hi)) hs))
        (Primrec.const none))
    apply Primrec.ite (he 2)
      (Primrec.ite hlen (Primrec.option_some.comp (Primrec.list_cons.comp
        (hadd.comp (hp.pair ((hg 0).pair (hg 1)))) hdrop)) (Primrec.const none))
    exact Primrec.ite (he 3)
      (Primrec.ite hlen (Primrec.option_some.comp (Primrec.list_cons.comp
        (hexp.comp (hp.pair ((hg 0).pair (hg 1)))) hdrop)) (Primrec.const none))
      (Primrec.const none)
  apply hraw.of_eq
  rintro ⟨p, ⟨tag, i⟩, stack⟩
  rcases tag with _ | _ | _ | _ | tag
  · rfl
  · simp [raw, processStep]
  · cases stack with
    | nil => simp [raw, processStep]
    | cons a stack => cases stack <;> simp [raw, processStep]
  · cases stack with
    | nil => simp [raw, processStep]
    | cons a stack => cases stack <;> simp [raw, processStep]
  · simp [raw, processStep]

theorem pr_processStack {σ α : Type} [Primcodable σ] [Primcodable α]
    (d : σ → Nat) (one : σ → α) (variableValue : σ → Nat → α)
    (addition exponential : σ → α → α → α)
    (hd : Primrec d) (hone : Primrec one)
    (hvar : Primrec (fun p : σ × Nat => variableValue p.1 p.2))
    (hadd : Primrec (fun p : σ × α × α => addition p.1 p.2.1 p.2.2))
    (hexp : Primrec (fun p : σ × α × α => exponential p.1 p.2.1 p.2.2)) :
    Primrec (fun p : σ × List Token =>
      processStack (one p.1) (variableValue p.1) (addition p.1) (exponential p.1)
        (d p.1) p.2) := by
  have hstep := pr_processStep d one variableValue addition exponential hd hone hvar hadd hexp
  unfold processStack
  apply Primrec.list_foldr (h := fun p q => q.2.bind
    (processStep (one p.1) (variableValue p.1) (addition p.1) (exponential p.1) (d p.1) q.1))
    Primrec.snd (Primrec.const (some []))
  apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
  refine (hstep.comp (g := fun p : ((σ × List Token) × Token × Option (List α)) × List α =>
    (p.1.1.1, p.1.2.1, p.2)) ?_).to₂
  exact (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

theorem pr_processCode {σ α : Type} [Primcodable σ] [Primcodable α]
    (d : σ → Nat) (one : σ → α) (variableValue : σ → Nat → α)
    (addition exponential : σ → α → α → α)
    (hd : Primrec d) (hone : Primrec one)
    (hvar : Primrec (fun p : σ × Nat => variableValue p.1 p.2))
    (hadd : Primrec (fun p : σ × α × α => addition p.1 p.2.1 p.2.2))
    (hexp : Primrec (fun p : σ × α × α => exponential p.1 p.2.1 p.2.2)) :
    Primrec (fun p : σ × List Nat =>
      processCode (one p.1) (variableValue p.1) (addition p.1) (exponential p.1)
        (d p.1) p.2) := by
  have hstack := pr_processStack d one variableValue addition exponential hd hone hvar hadd hexp
  have hs : Primrec (fun p : (σ × List Nat) × List Token =>
      processStack (one p.1.1) (variableValue p.1.1) (addition p.1.1)
        (exponential p.1.1) (d p.1.1) p.2) :=
    hstack.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.option_bind (pr_tokenize.comp Primrec.snd)
    (Primrec.option_bind hs (pr_singletonValue.comp Primrec.snd).to₂).to₂

theorem pr_oneRow : Primrec (fun p : Nat × Nat => oneRow p.1 p.2) := by
  unfold oneRow
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
  exact (pr_constantCode.comp ((Primrec.fst.comp Primrec.fst).pair
    (Primrec.snd.pair (Primrec.const 1)))).to₂

theorem pr_variableRow : Primrec (fun p : Nat × Nat × Nat => variableRow p.1 p.2.1 p.2.2) := by
  unfold variableRow
  apply Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  exact (pr_variableCode.comp ((Primrec.fst.comp Primrec.fst).pair
    (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂

theorem pr_additionRow :
    Primrec (fun p : Nat × Nat × List Nat × List Nat => additionRow p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold additionRow
  apply Primrec.list_map
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  have hd : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hb : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (pr_addCode.comp (hd.pair (Primrec.snd.pair
    (((Primrec.list_getD 0).comp ha Primrec.snd).pair
      ((Primrec.list_getD 0).comp hb Primrec.snd))))).to₂

private theorem pr_productCode :
    Primrec (fun p : Nat × Nat × Nat × Nat =>
      exponentialProductCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  ExponentialNormalFormProductCodeProof.actualPrimitiveRecursion

-- Keep the already certified numeric programs as heads during composition
-- elaboration. This is local transparency control; the kernel, theorem target,
-- axiom policy and all resource budgets are unchanged.
attribute [local irreducible] zeroCode exponentialProductCode

def exponentialStep (p : (Nat × Nat × List Nat × List Nat) × Nat) : Nat :=
  if p.2 = 0 then zeroCode p.1.1 0 else
    exponentialProductCode p.1.1 (p.2 - 1)
      (p.1.2.2.1.getD (p.2 - 1) 0) (p.1.2.2.2.getD (p.2 - 1) 0)

def exponentialStepInput (p : (Nat × Nat × List Nat × List Nat) × Nat) : Nat × Nat × Nat × Nat :=
  (p.1.1, p.2 - 1, p.1.2.2.1.getD (p.2 - 1) 0, p.1.2.2.2.getD (p.2 - 1) 0)

theorem pr_exponentialStepInput : Primrec exponentialStepInput := by
  have hd : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hb : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hpred : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  exact hd.pair (hpred.pair
    (((Primrec.list_getD 0).comp ha hpred).pair ((Primrec.list_getD 0).comp hb hpred)))

theorem pr_exponentialStepBody : Primrec (fun p =>
    exponentialProductCode (exponentialStepInput p).1 (exponentialStepInput p).2.1
      (exponentialStepInput p).2.2.1 (exponentialStepInput p).2.2.2) :=
  pr_productCode.comp (g := exponentialStepInput) pr_exponentialStepInput

def exponentialStepRaw (p : (Nat × Nat × List Nat × List Nat) × Nat) : Nat :=
  if p.2 = 0 then zeroCode p.1.1 0 else
    exponentialProductCode (exponentialStepInput p).1 (exponentialStepInput p).2.1
      (exponentialStepInput p).2.2.1 (exponentialStepInput p).2.2.2

theorem exponentialStepRaw_eq (p : (Nat × Nat × List Nat × List Nat) × Nat) :
    exponentialStepRaw p = exponentialStep p := rfl

theorem pr_exponentialZero : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat =>
    zeroCode p.1.1 0) := by
  have hd : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  exact ExponentialHereditaryCodecProof.pr_zeroCode.comp
    (g := fun p : (Nat × Nat × List Nat × List Nat) × Nat => (p.1.1,0))
    (hd.pair (Primrec.const 0))

theorem pr_exponentialPredicate : PrimrecPred (fun p : (Nat × Nat × List Nat × List Nat) × Nat =>
    p.2 = 0) :=
  Primrec.eq.comp Primrec.snd (Primrec.const 0)

theorem pr_exponentialStepRaw : Primrec exponentialStepRaw :=
  Primrec.ite (c := fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.2 = 0)
    (f := fun p => zeroCode p.1.1 0)
    (g := fun p => exponentialProductCode (exponentialStepInput p).1 (exponentialStepInput p).2.1
      (exponentialStepInput p).2.2.1 (exponentialStepInput p).2.2.2)
    pr_exponentialPredicate pr_exponentialZero pr_exponentialStepBody

theorem pr_exponentialStep : Primrec exponentialStep :=
  Primrec.of_eq (f := exponentialStepRaw) (g := exponentialStep)
    pr_exponentialStepRaw exponentialStepRaw_eq

theorem exponentialRow_eq_map (p : Nat × Nat × List Nat × List Nat) :
    exponentialRow p.1 p.2.1 p.2.2.1 p.2.2.2 =
      (List.range (p.2.1 + 1)).map (fun k => exponentialStep (p,k)) := by
  apply List.map_congr_left
  intro k _
  cases k <;> rfl

theorem pr_exponentialRow :
    Primrec (fun p : Nat × Nat × List Nat × List Nat => exponentialRow p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Nat × Nat × List Nat × List Nat =>
      (List.range (p.2.1 + 1)).map (fun k => exponentialStep (p,k))) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
      pr_exponentialStep.to₂
  exact hr.of_eq (fun p => (exponentialRow_eq_map p).symm)

theorem pr_variableRow_grouped :
    Primrec (fun p : (Nat × Nat) × Nat => variableRow p.1.1 p.1.2 p.2) := by
  have ht : Primrec (fun p : (Nat × Nat) × Nat => (p.1.1,p.1.2,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  exact pr_variableRow.comp (g := fun p : (Nat × Nat) × Nat => (p.1.1,p.1.2,p.2)) ht

theorem pr_additionRow_grouped :
    Primrec (fun p : (Nat × Nat) × List Nat × List Nat =>
      additionRow p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : (Nat × Nat) × List Nat × List Nat =>
      (p.1.1,p.1.2,p.2.1,p.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.snd.comp Primrec.snd)))
  exact pr_additionRow.comp (g := fun p : (Nat × Nat) × List Nat × List Nat =>
    (p.1.1,p.1.2,p.2.1,p.2.2)) ht

theorem pr_exponentialRow_grouped :
    Primrec (fun p : (Nat × Nat) × List Nat × List Nat =>
      exponentialRow p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : (Nat × Nat) × List Nat × List Nat =>
      (p.1.1,p.1.2,p.2.1,p.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.snd.comp Primrec.snd)))
  exact pr_exponentialRow.comp (g := fun p : (Nat × Nat) × List Nat × List Nat =>
    (p.1.1,p.1.2,p.2.1,p.2.2)) ht

theorem pr_rowProcessCode :
    Primrec (fun p : (Nat × Nat) × List Nat =>
      processCode (oneRow p.1.1 p.1.2) (variableRow p.1.1 p.1.2)
        (additionRow p.1.1 p.1.2) (exponentialRow p.1.1 p.1.2) p.1.1 p.2) :=
  pr_processCode (fun p : Nat × Nat => p.1) (fun p => oneRow p.1 p.2)
    (fun p => variableRow p.1 p.2) (fun p => additionRow p.1 p.2)
    (fun p => exponentialRow p.1 p.2) Primrec.fst pr_oneRow
    pr_variableRow_grouped pr_additionRow_grouped pr_exponentialRow_grouped

theorem pr_rowSource :
    Primrec (fun p : Nat × Nat × List Nat =>
      processCode (oneRow p.1 p.2.1) (variableRow p.1 p.2.1)
        (additionRow p.1 p.2.1) (exponentialRow p.1 p.2.1) p.1 p.2.2) := by
  have ht : Primrec (fun p : Nat × Nat × List Nat => ((p.1,p.2.1),p.2.2)) :=
    (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  exact pr_rowProcessCode.comp (g := fun p : Nat × Nat × List Nat => ((p.1,p.2.1),p.2.2)) ht

theorem pr_compileAt :
    Primrec (fun p : Nat × Nat × List Nat => compileAt p.1 p.2.1 p.2.2) :=
  Primrec.option_map pr_rowSource
    ((Primrec.list_getD 0).comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to₂

private theorem pr_max : Primrec (fun p : Nat × Nat => max p.1 p.2) := by
  apply (Primrec.ite (Primrec.nat_le.comp Primrec.fst Primrec.snd)
    Primrec.snd Primrec.fst).of_eq
  intro p
  by_cases h : p.1 ≤ p.2
  · simp [h, Nat.max_eq_right h]
  · simp [h, Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))]

theorem pr_depthCode : Primrec (fun p : Nat × List Nat => depthCode p.1 p.2) := by
  have hadd : Primrec (fun p : Nat × Nat × Nat => max p.2.1 p.2.2) :=
    pr_max.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))
  exact pr_processCode (fun d : Nat => d) (fun _ => 0) (fun _ _ => 0)
    (fun _ => Nat.max) (fun _ a b => max a b + 1)
    Primrec.id (Primrec.const 0) (Primrec.const 0) hadd (Primrec.succ.comp hadd)

theorem pr_normalizeCode : Primrec (fun p : Nat × List Nat => normalizeCode p.1 p.2) := by
  have hc : Primrec (fun p : (Nat × List Nat) × Nat => compileAt p.1.1 p.2 p.1.2) :=
    pr_compileAt.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))
  have hp : Primrec₂ (fun p : (Nat × List Nat) × Nat => fun n : Nat => (p.2, n)) :=
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  have hg := Primrec.option_bind pr_depthCode (Primrec.option_map hc hp).to₂
  apply hg.of_eq
  rintro ⟨d, raw⟩
  simp [normalizeCode, Option.map_eq_bind]

theorem actualPrimitivePrograms : Comparators.ExponentialNormalizerProgram.ActualPrimitivePrograms :=
  ⟨pr_compileAt, pr_depthCode, pr_normalizeCode⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramEffectivity
