module

public import LogicLineages.ComputabilityKnowledge.Comparators.CircuitReductionEffectivity

@[expose] public section

/-! External Codex continuation: explicit-code faithfulness and primitive-recursive
implementation certificate. The frozen semantic compiler and codec are unchanged.
Intermediate lemmas are not acceptance of the complete effectivity target. -/
namespace LogicLineages.ComputabilityKnowledge.CircuitReductionEffectivityProof

open PositiveExpression CircuitReduction

private theorem decode_encode_gates (gs : List Gate) : decodeGates (encodeGates gs) = some gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [encodeGates, encodeGate, decodeGates, ih]

theorem inputCodecFaithful : Comparators.CircuitReductionEffectivity.InputCodecFaithful := by
  intro c
  simp [decodeCircuit, encodeCircuit, decode_encode_gates]

private theorem expression_prefix (a : Expr Nat) :
    ∀ (b : Expr Nat) (r s : List Nat), encodeExpr a ++ r = encodeExpr b ++ s → a = b ∧ r = s := by
  induction a with
  | one =>
    intro b r s h
    cases b <;> simp [encodeExpr] at h
    exact ⟨rfl, h⟩
  | var i =>
    intro b r s h
    cases b <;> simp [encodeExpr] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, h⟩
  | add a b ha hb =>
    intro e r s h
    cases e with
    | one => simp [encodeExpr] at h
    | var i => simp [encodeExpr] at h
    | emul c d => simp [encodeExpr] at h
    | add c d =>
      simp only [encodeExpr, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨hac, hrest⟩ := ha c (encodeExpr b ++ r) (encodeExpr d ++ s) h
      obtain ⟨hbd, hrs⟩ := hb d r s hrest
      cases hac
      cases hbd
      exact ⟨rfl, hrs⟩
  | emul a b ha hb =>
    intro e r s h
    cases e with
    | one => simp [encodeExpr] at h
    | var i => simp [encodeExpr] at h
    | add c d => simp [encodeExpr] at h
    | emul c d =>
      simp only [encodeExpr, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨hac, hrest⟩ := ha c (encodeExpr b ++ r) (encodeExpr d ++ s) h
      obtain ⟨hbd, hrs⟩ := hb d r s hrest
      cases hac
      cases hbd
      exact ⟨rfl, hrs⟩

theorem outputCodecFaithful : Comparators.CircuitReductionEffectivity.OutputCodecFaithful := by
  intro as bs h
  induction as generalizing bs with
  | nil => cases bs <;> simp [encodeSystem] at h ⊢
  | cons a as ih =>
    cases bs with
    | nil => simp [encodeSystem] at h
    | cons b bs =>
      simp only [encodeSystem, List.cons.injEq] at h
      have hp := h.2.2
      simp only [List.append_assoc] at hp
      obtain ⟨ha, hp⟩ := expression_prefix a.1 b.1 _ _ hp
      obtain ⟨hb, hp⟩ := expression_prefix a.2 b.2 _ _ hp
      have hab : a = b := Prod.ext ha hb
      exact congrArg₂ List.cons hab (ih hp)

theorem codeCorrespondence : Comparators.CircuitReductionEffectivity.CodeCorrespondence := by
  intro c
  simp [compileCode, inputCodecFaithful c]

private def gateEquiv : Gate ≃ Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)) where
  toFun
    | .constant k => .inl k
    | .add x y => .inr (.inl (x,y))
    | .mul x y => .inr (.inr (x,y))
  invFun
    | .inl k => .constant k
    | .inr (.inl (x,y)) => .add x y
    | .inr (.inr (x,y)) => .mul x y
  left_inv := by intro g; cases g <;> rfl
  right_inv := by intro v; rcases v with k | (⟨x,y⟩ | ⟨x,y⟩) <;> rfl

private instance gatePrimcodable : Primcodable Gate := Primcodable.ofEquiv _ gateEquiv

private theorem pr_gateToCode : Primrec gateEquiv := Primrec.of_equiv
private theorem pr_gateFromCode : Primrec gateEquiv.symm := Primrec.of_equiv_symm

private theorem pr_constant : Primrec Gate.constant :=
  pr_gateFromCode.comp Primrec.sumInl
private theorem pr_add : Primrec (fun p : Nat × Nat => Gate.add p.1 p.2) :=
  pr_gateFromCode.comp (Primrec.sumInr.comp Primrec.sumInl)
private theorem pr_mul : Primrec (fun p : Nat × Nat => Gate.mul p.1 p.2) :=
  pr_gateFromCode.comp (Primrec.sumInr.comp Primrec.sumInr)

private theorem pr_gateCases {α σ : Type} [Primcodable α] [Primcodable σ]
    (f : α → Gate) (c : α → Nat → σ) (a m : α → Nat × Nat → σ)
    (hf : Primrec f) (hc : Primrec₂ c) (ha : Primrec₂ a) (hm : Primrec₂ m) :
    Primrec (fun x => match f x with
      | .constant k => c x k
      | .add u v => a x (u,v)
      | .mul u v => m x (u,v)) := by
  have h := Primrec.sumCasesOn (pr_gateToCode.comp hf) hc
    (Primrec.sumCasesOn Primrec.snd
      (ha.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hm.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact h.of_eq (fun x => by cases f x <;> rfl)

private theorem pr_cons {α : Type} [Primcodable α] {a : α → Nat} {b : α → List Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => a x :: b x) :=
  Primrec.list_cons.comp ha hb

private theorem pr_positiveNumeral : Primrec (fun k => encodeExpr (positiveNumeral k)) := by
  have h : Primrec (Nat.rec ([0] : List Nat) (fun _ r => 2 :: (r ++ [0]))) :=
    Primrec.nat_rec₁ [0] (pr_cons (Primrec.const 2)
      (Primrec.list_append.comp Primrec.snd (Primrec.const [0]))).to₂
  apply h.of_eq
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [positiveNumeral, encodeExpr, ih]

private theorem pr_renamedExpr {α ι : Type} [Primcodable α]
    (e : Expr ι) (f : α → ι → Nat) (hf : ∀ i, Primrec (fun x => f x i)) :
    Primrec (fun x => encodeExpr (e.rename (f x))) := by
  induction e with
  | one => exact Primrec.const [0]
  | var i => exact pr_cons (Primrec.const 1) (pr_cons (hf i) (Primrec.const []))
  | add a b ha hb => exact pr_cons (Primrec.const 2) (Primrec.list_append.comp ha hb)
  | emul a b ha hb => exact pr_cons (Primrec.const 3) (Primrec.list_append.comp ha hb)

private theorem encodeSystem_append (s t : System) : encodeSystem (s ++ t) = encodeSystem s ++ encodeSystem t := by
  induction s with
  | nil => rfl
  | cons p ps ih => simp [encodeSystem, ih, List.append_assoc]


private theorem pr_fixedSystem {α ι : Type} [Primcodable α]
    (sys : List (Expr ι × Expr ι)) (f : α → ι → Nat)
    (hf : ∀ i, Primrec (fun x => f x i)) :
    Primrec (fun x => encodeSystem (sys.map (fun p => (p.1.rename (f x), p.2.rename (f x))))) := by
  induction sys with
  | nil => exact Primrec.const []
  | cons p ps ih =>
    have ha := pr_renamedExpr p.1 f hf
    have hb := pr_renamedExpr p.2 f hf
    exact pr_cons (Primrec.list_length.comp ha) (pr_cons (Primrec.list_length.comp hb)
      (Primrec.list_append.comp (Primrec.list_append.comp ha hb) ih))

private theorem pr_gadgetNames {α : Type} [Primcodable α]
    {x y w b i : α → Nat} (hx : Primrec x) (hy : Primrec y) (hw : Primrec w)
    (hb : Primrec b) (hi : Primrec i) (v : Comparators.MultiplicationGadget.Variable) :
    Primrec (fun a => gadgetNames (x a) (y a) (w a) (b a) (i a) v) := by
  cases v
  · exact hx
  · exact hy
  · exact hw
  all_goals
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp hb (Primrec.nat_mul.comp (Primrec.const 8) hi)) (Primrec.const _)

private theorem pr_gateSystem :
    Primrec (fun p : Nat × Nat × Nat × Gate => encodeSystem (gateEquations p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  refine (pr_gateCases (α := Nat × Nat × Nat × Gate) (fun p => p.2.2.2)
    (fun p k => encodeSystem [(.var p.1, positiveNumeral k)])
    (fun p xy => encodeSystem [(.var p.1, .add (.var xy.1) (.var xy.2))])
    (fun p xy => encodeSystem (Comparators.MultiplicationGadget.equations.map
      (fun q => (q.1.rename (gadgetNames xy.1 xy.2 p.1 p.2.1 p.2.2.1),
        q.2.rename (gadgetNames xy.1 xy.2 p.1 p.2.1 p.2.2.1)))))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) ?_ ?_ ?_).of_eq ?_
  · have hn := pr_positiveNumeral.comp (Primrec.snd : Primrec (fun p : (Nat × Nat × Nat × Gate) × Nat => p.2))
    have hw : Primrec (fun p : (Nat × Nat × Nat × Gate) × Nat => [1, p.1.1]) :=
      pr_cons (Primrec.const 1) (pr_cons (Primrec.fst.comp Primrec.fst) (Primrec.const []))
    simpa [encodeSystem, encodeExpr] using
      (pr_cons (Primrec.const 2) (pr_cons (Primrec.list_length.comp hn)
        (Primrec.list_append.comp hw hn))).to₂
  · have hw : Primrec (fun p : (Nat × Nat × Nat × Gate) × (Nat × Nat) => [1, p.1.1]) :=
      pr_cons (Primrec.const 1) (pr_cons (Primrec.fst.comp Primrec.fst) (Primrec.const []))
    have hx : Primrec (fun p : (Nat × Nat × Nat × Gate) × (Nat × Nat) => [1, p.2.1]) :=
      pr_cons (Primrec.const 1) (pr_cons (Primrec.fst.comp Primrec.snd) (Primrec.const []))
    have hy : Primrec (fun p : (Nat × Nat × Nat × Gate) × (Nat × Nat) => [1, p.2.2]) :=
      pr_cons (Primrec.const 1) (pr_cons (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    simpa [encodeSystem, encodeExpr] using
      (pr_cons (Primrec.const 2) (pr_cons (Primrec.const 5)
        (Primrec.list_append.comp hw (pr_cons (Primrec.const 2) (Primrec.list_append.comp hx hy))))).to₂
  · apply pr_fixedSystem
    intro v
    exact pr_gadgetNames (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) v
  · intro p
    cases p.2.2.2 <;> rfl

/-- An indexed list recursion, justified by an actual primitive-recursive
well-founded recursion theorem rather than by executability of the definition. -/
private theorem pr_indexedList {δ β σ : Type} [Primcodable δ] [Primcodable β]
    [Primcodable σ] [Inhabited β] [Inhabited σ]
    (f : δ → Nat → List β → σ) (initial : δ → σ) (step : δ → Nat → β → σ → σ)
    (hinit : Primrec initial)
    (hstep : Primrec (fun p : δ × Nat × β × σ => step p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hnil : ∀ d n, f d n [] = initial d)
    (hcons : ∀ d n b bs, f d n (b :: bs) = step d n b (f d (n + 1) bs)) :
    Primrec (fun p : δ × Nat × List β => f p.1 p.2.1 p.2.2) := by
  let children : (δ × Nat × List β) → List (δ × Nat × List β) := fun p =>
    if p.2.2.length = 0 then [] else [(p.1, p.2.1 + 1, p.2.2.tail)]
  let assemble : (δ × Nat × List β) → List σ → Option σ := fun p rs =>
    some (if p.2.2.length = 0 then initial p.1 else step p.1 p.2.1 p.2.2.head! rs.head!)
  have hlist : Primrec (fun p : δ × Nat × List β => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlen := Primrec.list_length.comp hlist
  have hzero := Primrec.eq.comp hlen (Primrec.const 0)
  have hchildren : Primrec children :=
    Primrec.ite hzero (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec.fst.pair ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.list_tail.comp hlist))) (Primrec.const []))
  have hassemble : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite (hzero.comp Primrec.fst)
    · exact hinit.comp (Primrec.fst.comp Primrec.fst)
    · exact hstep.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.list_headI.comp (hlist.comp Primrec.fst)).pair
            (Primrec.list_headI.comp Primrec.snd))))
  apply Primrec.nat_omega_rec' (fun p : δ × Nat × List β => f p.1 p.2.1 p.2.2)
    hlen hchildren hassemble
  · intro p p' hp
    rcases p with ⟨d,n,bs⟩
    cases bs with
    | nil => simp [children] at hp
    | cons b bs =>
      simp [children] at hp
      subst p'
      simp
  · intro p
    rcases p with ⟨d,n,bs⟩
    cases bs with
    | nil => simp [assemble, children, hnil]
    | cons b bs => simp [assemble, children, hcons]

local instance : Inhabited Gate := ⟨.constant 0⟩

private theorem pr_compiledGates :
    Primrec (fun p : Nat × Nat × Nat × List Gate => encodeSystem (compileGates p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  let f : (Nat × Nat × Nat) → Nat → List Gate → List Nat := fun d k gs =>
    encodeSystem (compileGates d.1 (d.2.1 + k) (d.2.2 + k) gs)
  let step : (Nat × Nat × Nat) → Nat → Gate → List Nat → List Nat := fun d k g out =>
    encodeSystem (gateEquations (d.2.1 + k) d.1 (d.2.2 + k) g) ++ out
  have hs : Primrec (fun p : (Nat × Nat × Nat) × Nat × Gate × List Nat =>
      step p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    apply Primrec.list_append.comp _ (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    refine pr_gateSystem.comp (g := fun p : (Nat × Nat × Nat) × Nat × Gate × List Nat =>
      (p.1.2.1 + p.2.1, p.1.1, p.1.2.2 + p.2.1, p.2.2.1)) ?_
    exact (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hf := pr_indexedList f (fun _ => []) step (Primrec.const []) hs
    (fun _ _ => rfl) (by intro d k g gs; simp [f, step, compileGates, encodeSystem_append, Nat.add_assoc])
  have hp : Primrec (fun p : Nat × Nat × Nat × List Gate =>
      ((p.1,p.2.1,p.2.2.1),0,p.2.2.2)) :=
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
      ((Primrec.const 0).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (hf.comp hp).of_eq (fun _ => by simp [f])


private def parseGate (tag x y : Nat) : Option Gate :=
  if tag = 0 then (if y = 0 then some (.constant x) else none)
  else if tag = 1 then some (.add x y)
  else if tag = 2 then some (.mul x y) else none

private theorem pr_parseGate : Primrec (fun p : Nat × Nat × Nat => parseGate p.1 p.2.1 p.2.2) := by
  apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
  · exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
      (Primrec.option_some.comp (pr_constant.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const none)
  · apply Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
    · exact Primrec.option_some.comp (pr_add.comp Primrec.snd)
    · exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2))
        (Primrec.option_some.comp (pr_mul.comp Primrec.snd)) (Primrec.const none)

private theorem pr_optionCons : Primrec (fun p : Option Gate × Option (List Gate) =>
    p.1.bind (fun g => p.2.map (g :: ·))) := by
  apply Primrec.option_bind Primrec.fst
  apply Primrec.option_map (Primrec.snd.comp Primrec.fst)
  exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private theorem decode_cons (x : Nat) (xs : List Nat) :
    decodeGates (x :: xs) =
      if 2 ≤ xs.length then (parseGate x (xs.getD 0 0) (xs.getD 1 0)).bind
        (fun g => (decodeGates (xs.drop 2)).map (g :: ·)) else none := by
  cases xs with
  | nil => simp [decodeGates]
  | cons y ys =>
    cases ys with
    | nil => simp [decodeGates]
    | cons z zs =>
      cases x with
      | zero => cases z <;> simp [decodeGates, parseGate]
      | succ x =>
        cases x with
        | zero => simp [decodeGates, parseGate]
        | succ x => cases x <;> simp [decodeGates, parseGate]

private abbrev DecodeCache := Option (List Gate) × Option (List Gate) × Option (List Gate)

private def decodeCacheStep (p : Nat × List Nat × DecodeCache) : DecodeCache :=
  ((if 2 ≤ p.2.1.length then (parseGate p.1 (p.2.1.getD 0 0) (p.2.1.getD 1 0)).bind
    (fun g => p.2.2.2.2.map (g :: ·)) else none), p.2.2.1, p.2.2.2.1)

private theorem pr_decodeCacheStep : Primrec decodeCacheStep := by
  apply Primrec.pair
  · apply Primrec.ite (Primrec.nat_le.comp (Primrec.const 2)
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    · refine pr_optionCons.comp (g := fun p : Nat × List Nat × DecodeCache =>
        (parseGate p.1 (p.2.1.getD 0 0) (p.2.1.getD 1 0), p.2.2.2.2)) ?_
      apply Primrec.pair
      · refine pr_parseGate.comp (g := fun p : Nat × List Nat × DecodeCache =>
          (p.1, p.2.1.getD 0 0, p.2.1.getD 1 0)) ?_
        exact Primrec.fst.pair
          (((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).pair
            ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
      · exact Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    · exact Primrec.const none
  · exact (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private def decodeCache (xs : List Nat) : DecodeCache :=
  (decodeGates xs, decodeGates xs.tail, decodeGates xs.tail.tail)

private theorem decodeCache_cons (x : Nat) (xs : List Nat) :
    decodeCache (x :: xs) = decodeCacheStep (x,xs,decodeCache xs) := by
  apply Prod.ext
  · have hdrop : xs.drop 2 = xs.tail.tail := by
      cases xs with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    simpa [decodeCache, decodeCacheStep, hdrop] using decode_cons x xs
  · rfl

private theorem pr_decodeGates : Primrec decodeGates := by
  have hrec : Primrec (fun xs : List Nat =>
      List.recOn (motive := fun _ => DecodeCache) xs (some [],some [],some [])
        (fun x ys cache => decodeCacheStep (x,ys,cache))) :=
    Primrec.list_rec Primrec.id (Primrec.const (some [],some [],some []))
      (pr_decodeCacheStep.comp Primrec.snd).to₂
  have hcache : Primrec decodeCache := by
    apply hrec.of_eq
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.recOn, ih]
      exact (decodeCache_cons x xs).symm
  exact Primrec.fst.comp hcache

private theorem pr_outputEqualityCode : Primrec (fun p : Nat × Nat =>
    encodeSystem [(.var p.1, .var p.2)]) := by
  exact pr_cons (Primrec.const 2) (pr_cons (Primrec.const 2)
    (pr_cons (Primrec.const 1) (pr_cons Primrec.fst
      (pr_cons (Primrec.const 1) (pr_cons Primrec.snd (Primrec.const []))))))

private theorem pr_compiledCircuit : Primrec (fun p : Nat × List Gate × Nat × Nat =>
    encodeSystem (compile ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩)) := by
  have h : Primrec (fun p : Nat × List Gate × Nat × Nat =>
      encodeSystem (compileGates (p.1 + p.2.1.length) p.1 0 p.2.1) ++
        encodeSystem [(.var p.2.2.1, .var p.2.2.2)]) := by
    apply Primrec.list_append.comp
    · refine pr_compiledGates.comp (g := fun p : Nat × List Gate × Nat × Nat =>
        (p.1 + p.2.1.length, p.1, 0, p.2.1)) ?_
      exact (Primrec.nat_add.comp Primrec.fst
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))).pair
          (Primrec.fst.pair ((Primrec.const 0).pair (Primrec.fst.comp Primrec.snd)))
    · exact pr_outputEqualityCode.comp (Primrec.snd.comp Primrec.snd)
  exact h.of_eq (fun _ => by simp [compile, encodeSystem_append])

theorem compilerPrimrec : Primrec compileCode := by
  have hg (i : Nat) : Primrec (fun xs : List Nat => xs.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)
  have hd : Primrec (fun xs : List Nat => decodeGates (xs.drop 3)) :=
    pr_decodeGates.comp (Primrec.list_drop.comp (Primrec.const 3) Primrec.id)
  have h : Primrec (fun xs : List Nat => if 3 ≤ xs.length then
      (decodeGates (xs.drop 3)).map (fun gs => encodeSystem
        (compile ⟨xs.getD 0 0,gs,xs.getD 1 0,xs.getD 2 0⟩)) else none) := by
    apply Primrec.ite (Primrec.nat_le.comp (Primrec.const 3) Primrec.list_length)
    · apply Primrec.option_map hd
      refine pr_compiledCircuit.comp (g := fun p : List Nat × List Gate =>
        (p.1.getD 0 0, p.2, p.1.getD 1 0, p.1.getD 2 0)) ?_
      exact ((hg 0).comp Primrec.fst).pair
        (Primrec.snd.pair (((hg 1).comp Primrec.fst).pair ((hg 2).comp Primrec.fst)))
    · exact Primrec.const none
  apply h.of_eq
  intro xs
  cases xs with
  | nil => rfl
  | cons n xs =>
    cases xs with
    | nil => rfl
    | cons l xs =>
      cases xs with
      | nil => rfl
      | cons r xs => simp [compileCode, decodeCircuit, Option.map_map, Function.comp_def]

theorem circuitReductionEffectivity : Comparators.CircuitReductionEffectivity.Target :=
  ⟨inputCodecFaithful, outputCodecFaithful, codeCorrespondence, compilerPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.CircuitReductionEffectivityProof
