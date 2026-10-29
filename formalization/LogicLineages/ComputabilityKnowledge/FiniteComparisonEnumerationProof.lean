module

public import LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumeration

@[expose] public section

/-! External Codex continuation: exact prefix decoding, stack evaluation and
finite positive tuple enumeration. All counterexample predicates remain the
independently frozen source semantics, including malformed-code rejection. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof

open PositiveExpression CircuitReduction FiniteComparisonEnumeration

private def tokenCode (t : Token) : List Nat :=
  match t.1 with | 0 => [0] | 1 => [1,t.2] | 2 => [2] | 3 => [3] | _ => []
private def tokenCodes (ts : List Token) : List Nat := ts.flatMap tokenCode
private def stackCode (es : List (Expr Nat)) : List Nat := es.flatMap encodeExpr
private def BoundedStack (d : Nat) (es : List (Expr Nat)) : Prop := ∀ e ∈ es, Bounded d e

private theorem token_prepend (t : Token) (xs : List Nat) (ts : List Token)
    (ih : ∀ rs, tokenize xs = some rs → tokenCodes rs = xs)
    (h : (tokenize xs).map (t :: ·) = some ts) : tokenCodes ts = tokenCode t ++ xs := by
  cases hr : tokenize xs with
  | none => simp [hr] at h
  | some rs =>
    simp [hr] at h
    subst ts
    simp only [tokenCodes,List.flatMap_cons]
    rw [show rs.flatMap tokenCode = xs from ih rs hr]

private theorem tokenize_sound : ∀ (xs : List Nat) (ts : List Token),
    tokenize xs = some ts → tokenCodes ts = xs
  | [],ts,h => by simp [tokenize] at h; subst ts; rfl
  | 0::xs,ts,h => by simpa [tokenCode] using token_prepend (0,0) xs ts (tokenize_sound xs) h
  | 1::i::xs,ts,h => by simpa [tokenCode] using token_prepend (1,i) xs ts (tokenize_sound xs) h
  | 2::xs,ts,h => by simpa [tokenCode] using token_prepend (2,0) xs ts (tokenize_sound xs) h
  | 3::xs,ts,h => by simpa [tokenCode] using token_prepend (3,0) xs ts (tokenize_sound xs) h
  | [1],_,h => by simp [tokenize] at h
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))::_,_,h => by simp [tokenize] at h

private def tokens : Expr Nat → List Token
  | .one => [(0,0)]
  | .var i => [(1,i)]
  | .add a b => (2,0) :: (tokens a ++ tokens b)
  | .emul a b => (3,0) :: (tokens a ++ tokens b)

private theorem tokenize_prefix (e : Expr Nat) (rest : List Nat) :
    tokenize (encodeExpr e ++ rest) = (tokenize rest).map (fun ts => tokens e ++ ts) := by
  induction e generalizing rest with
  | one => rfl
  | var i => rfl
  | add a b ha hb =>
    simp [encodeExpr,tokens,tokenize,List.append_assoc,ha,hb,Option.map_map,Function.comp_def]
  | emul a b ha hb =>
    simp [encodeExpr,tokens,tokenize,List.append_assoc,ha,hb,Option.map_map,Function.comp_def]

private theorem tokenize_encode (e : Expr Nat) : tokenize (encodeExpr e) = some (tokens e) := by
  simpa [tokenize] using tokenize_prefix e []

private theorem syntax_step_sound (d : Nat) (t : Token) (es out : List (Expr Nat))
    (hb : BoundedStack d es) (h : syntaxStep d t es = some out) :
    stackCode out = tokenCode t ++ stackCode es ∧ BoundedStack d out := by
  rcases t with ⟨tag,i⟩
  cases tag with
  | zero =>
    simp only [syntaxStep] at h
    cases h
    constructor
    · simp [stackCode,tokenCode,encodeExpr]
    · simpa [BoundedStack,Bounded] using hb
  | succ tag =>
    cases tag with
    | zero =>
      by_cases hi : i < d
      · simp only [syntaxStep,if_pos hi] at h
        cases h
        constructor
        · simp [stackCode,tokenCode,encodeExpr]
        · simpa [BoundedStack,Bounded] using And.intro hi hb
      · simp [syntaxStep,hi] at h
    | succ tag =>
      cases tag with
      | zero =>
        cases es with
        | nil => simp [syntaxStep] at h
        | cons a es =>
          cases es with
          | nil => simp [syntaxStep] at h
          | cons b es =>
            simp only [syntaxStep] at h
            cases h
            constructor
            · simp [stackCode,tokenCode,encodeExpr,List.append_assoc]
            · simpa [BoundedStack,Bounded,and_assoc] using hb
      | succ tag =>
        cases tag with
        | zero =>
          cases es with
          | nil => simp [syntaxStep] at h
          | cons a es =>
            cases es with
            | nil => simp [syntaxStep] at h
            | cons b es =>
              simp only [syntaxStep] at h
              cases h
              constructor
              · simp [stackCode,tokenCode,encodeExpr,List.append_assoc]
              · simpa [BoundedStack,Bounded,and_assoc] using hb
        | succ tag => simp [syntaxStep] at h

private theorem syntax_stack_sound (d : Nat) (ts : List Token) (es : List (Expr Nat))
    (h : syntaxStack d ts = some es) : stackCode es = tokenCodes ts ∧ BoundedStack d es := by
  induction ts generalizing es with
  | nil =>
    simp [syntaxStack] at h
    subst es
    exact ⟨rfl,by simp [BoundedStack]⟩
  | cons t ts ih =>
    change (syntaxStack d ts).bind (syntaxStep d t) = some es at h
    cases hr : syntaxStack d ts with
    | none => simp [hr] at h
    | some rs =>
      have hi := ih rs hr
      have hs := syntax_step_sound d t rs es hi.2 (by simpa [hr] using h)
      refine ⟨?_,hs.2⟩
      rw [hs.1,hi.1]
      rfl

private theorem syntax_tokens (d : Nat) (e : Expr Nat) (hb : Bounded d e)
    (es : List (Expr Nat)) :
    (tokens e).foldr (fun t result => result.bind (syntaxStep d t)) (some es) = some (e::es) := by
  induction e generalizing es with
  | one => rfl
  | var i =>
    change i < d at hb
    simp [tokens,syntaxStep,hb]
  | add a b ha hb' =>
    simp only [tokens,List.foldr_cons,List.foldr_append]
    rw [hb' hb.2,ha hb.1]
    rfl
  | emul a b ha hb' =>
    simp only [tokens,List.foldr_cons,List.foldr_append]
    rw [hb' hb.2,ha hb.1]
    rfl

private theorem decode_encode (d : Nat) (e : Expr Nat) (hb : Bounded d e) :
    decodeExpr d (encodeExpr e) = some e := by
  unfold decodeExpr
  rw [tokenize_encode]
  change (syntaxStack d (tokens e)).bind (fun stack => match stack with | [e] => some e | _ => none) = some e
  rw [show syntaxStack d (tokens e) = some [e] from syntax_tokens d e hb []]
  rfl

theorem expressionDecoderExact : Comparators.FiniteComparisonEnumeration.ExpressionDecoderExact := by
  intro d xs e
  constructor
  · intro h
    unfold decodeExpr at h
    cases ht : tokenize xs with
    | none => simp [ht] at h
    | some ts =>
      cases hs : syntaxStack d ts with
      | none => simp [ht,hs] at h
      | some es =>
        cases es with
        | nil => simp [ht,hs] at h
        | cons a es =>
          cases es with
          | nil =>
            simp [ht,hs] at h
            subst a
            have hh := syntax_stack_sound d ts [e] hs
            refine ⟨?_,hh.2 e (by simp)⟩
            have hc := tokenize_sound xs ts ht
            simpa [stackCode] using hc.symm.trans hh.1.symm
          | cons b es => simp [ht,hs] at h
  · rintro ⟨rfl,hb⟩
    exact decode_encode d e hb

private theorem numeric_step_sim (d : Nat) (values : List Nat) (t : Token) (es : List (Expr Nat)) :
    numericStep d values t (es.map (fun e => e.eval (tupleValue values))) =
      (syntaxStep d t es).map (List.map (fun e => e.eval (tupleValue values))) := by
  rcases t with ⟨tag,i⟩
  cases tag with
  | zero => rfl
  | succ tag =>
    cases tag with
    | zero => by_cases hi : i < d <;> simp [numericStep,syntaxStep,hi,Expr.eval]
    | succ tag =>
      cases tag with
      | zero =>
        cases es with
        | nil => rfl
        | cons a es => cases es <;> rfl
      | succ tag =>
        cases tag with
        | zero =>
          cases es with
          | nil => rfl
          | cons a es => cases es <;> rfl
        | succ tag => rfl

private theorem numeric_stack_sim (d : Nat) (values : List Nat) (ts : List Token) :
    numericStack d values ts = (syntaxStack d ts).map (List.map (fun e => e.eval (tupleValue values))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (numericStack d values ts).bind (numericStep d values t) =
      ((syntaxStack d ts).bind (syntaxStep d t)).map _
    rw [ih]
    cases hs : syntaxStack d ts with
    | none => rfl
    | some es => exact numeric_step_sim d values t es

theorem evaluationCorrect : Comparators.FiniteComparisonEnumeration.EvaluationCorrect := by
  intro d xs values
  unfold evalCode decodeExpr
  cases ht : tokenize xs with
  | none => rfl
  | some ts =>
    change (numericStack d values ts).bind (fun stack => match stack with | [n] => some n | _ => none) =
      ((syntaxStack d ts).bind (fun stack => match stack with | [e] => some e | _ => none)).map
        (fun e => e.eval (tupleValue values))
    rw [numeric_stack_sim]
    cases hs : syntaxStack d ts with
    | none => rfl
    | some es =>
      cases es with
      | nil => rfl
      | cons e es => cases es <;> rfl

private theorem eval_congr_bounded (e : Expr Nat) (d : Nat) (ρ τ : Nat → PosNat)
    (hb : Bounded d e) (h : ∀ i, i < d → ρ i = τ i) : e.eval ρ = e.eval τ := by
  induction e with
  | one => rfl
  | var i => exact congrArg Subtype.val (h i hb)
  | add a b ha hb' =>
    change a.eval ρ + b.eval ρ = a.eval τ + b.eval τ
    rw [ha hb.1,hb' hb.2]
  | emul a b ha hb' =>
    change 2^a.eval ρ * b.eval ρ = 2^a.eval τ * b.eval τ
    rw [ha hb.1,hb' hb.2]

private theorem finite_tuple_eval (d : Nat) (e : Expr Nat) (hb : Bounded d e) (values : List Nat) :
    e.eval (tupleValue values) = e.eval (CircuitComparison.finiteVal (tupleOf d values)) := by
  apply eval_congr_bounded e d _ _ hb
  intro i hi
  simp [CircuitComparison.finiteVal,tupleOf,hi]

theorem finiteEvaluationCorrect : Comparators.FiniteComparisonEnumeration.FiniteEvaluationCorrect := by
  intro d e hb values
  rw [evaluationCorrect,decode_encode d e hb]
  simp only [Option.map_some]
  exact congrArg some (finite_tuple_eval d e hb values)

theorem tupleEnumerationSurjective : Comparators.FiniteComparisonEnumeration.TupleEnumerationSurjective := by
  intro d ρ
  let values := List.ofFn (fun i : Fin d => (ρ i).val - 1)
  refine ⟨Encodable.encode values,?_⟩
  funext i
  apply Subtype.ext
  simp only [enumTuple,enumValues,Encodable.encodek,Option.getD_some,tupleOf,tupleValue]
  have hg : values.getD i.val 0 = (ρ i).val - 1 := by simp [values,List.getD,i.isLt]
  rw [hg]
  have := (ρ i).property
  omega

theorem pairDecoderExact : Comparators.FiniteComparisonEnumeration.PairDecoderExact := by
  intro xs d a b
  constructor
  · intro h
    cases xs with
    | nil => simp [decodePair] at h
    | cons d' xs =>
      cases xs with
      | nil => simp [decodePair] at h
      | cons na xs =>
        cases xs with
        | nil => simp [decodePair] at h
        | cons nb rest =>
          by_cases hlen : rest.length = na+nb
          · cases ha : decodeExpr d' (rest.take na) with
            | none => simp [decodePair,hlen,ha] at h
            | some a' =>
              cases hb : decodeExpr d' (rest.drop na) with
              | none => simp [decodePair,hlen,ha,hb] at h
              | some b' =>
                simp [decodePair,hlen,ha,hb] at h
                rcases h with ⟨hd,haeq,hbeq⟩
                subst d'
                subst a'
                subst b'
                have hA := (expressionDecoderExact d _ a).mp ha
                have hB := (expressionDecoderExact d _ b).mp hb
                refine ⟨?_,hA.2,hB.2⟩
                have hna : (encodeExpr a).length = na := by rw [←hA.1,List.length_take]; omega
                have hnb : (encodeExpr b).length = nb := by rw [←hB.1,List.length_drop]; omega
                simp only [CircuitComparison.encodeComparison,encodeSystem,List.append_nil,hna,hnb]
                rw [←hA.1,←hB.1,List.take_append_drop]
          · simp [decodePair,hlen] at h
  · rintro ⟨rfl,ha,hb⟩
    simp [CircuitComparison.encodeComparison,encodeSystem,decodePair,
      decode_encode d a ha,decode_encode d b hb]

private theorem eval_pair_sim (xs values : List Nat) :
    evalPair xs values = (decodePair xs).map (fun p =>
      (p.2.1.eval (tupleValue values),p.2.2.eval (tupleValue values))) := by
  cases xs with
  | nil => rfl
  | cons d xs =>
    cases xs with
    | nil => rfl
    | cons na xs =>
      cases xs with
      | nil => rfl
      | cons nb rest =>
        by_cases hlen : rest.length = na+nb
        · simp only [evalPair,decodePair,if_pos hlen]
          rw [evaluationCorrect d (rest.take na) values, evaluationCorrect d (rest.drop na) values]
          cases ha : decodeExpr d (rest.take na) <;> cases hb : decodeExpr d (rest.drop na) <;> rfl
        · simp [evalPair,decodePair,hlen]

private theorem strict_check_decoded (xs : List Nat) (d : Nat) (a b : Expr Nat) (k : Nat)
    (hd : decodePair xs = some (d,a,b)) :
    checkStrict xs k = true ↔ ¬ a.eval (CircuitComparison.finiteVal (enumTuple d k)) <
      b.eval (CircuitComparison.finiteVal (enumTuple d k)) := by
  have hb := (pairDecoderExact xs d a b).mp hd
  simp only [checkStrict,eval_pair_sim,hd,Option.map_some]
  rw [finite_tuple_eval d a hb.2.1,finite_tuple_eval d b hb.2.2]
  simp only [decide_eq_true_eq,enumTuple]

private theorem weak_check_decoded (xs : List Nat) (d : Nat) (a b : Expr Nat) (k : Nat)
    (hd : decodePair xs = some (d,a,b)) :
    checkWeak xs k = true ↔ ¬ a.eval (CircuitComparison.finiteVal (enumTuple d k)) ≤
      b.eval (CircuitComparison.finiteVal (enumTuple d k)) := by
  have hb := (pairDecoderExact xs d a b).mp hd
  simp only [checkWeak,eval_pair_sim,hd,Option.map_some]
  rw [finite_tuple_eval d a hb.2.1,finite_tuple_eval d b hb.2.2]
  simp only [decide_eq_true_eq,enumTuple]

theorem counterexampleEnumeration : Comparators.FiniteComparisonEnumeration.CounterexampleEnumeration := by
  constructor
  · intro xs
    constructor
    · rintro ⟨d,a,b,hcode,ha,hb,ρ,hbad⟩
      obtain ⟨k,hk⟩ := tupleEnumerationSurjective d ρ
      refine ⟨k,(strict_check_decoded xs d a b k ((pairDecoderExact xs d a b).mpr ⟨hcode,ha,hb⟩)).mpr ?_⟩
      simpa [hk] using hbad
    · rintro ⟨k,hk⟩
      cases hd : decodePair xs with
      | none => simp [checkStrict,eval_pair_sim,hd] at hk
      | some pair =>
        rcases pair with ⟨d,a,b⟩
        obtain ⟨hcode,ha,hb⟩ := (pairDecoderExact xs d a b).mp hd
        exact ⟨d,a,b,hcode,ha,hb,enumTuple d k,(strict_check_decoded xs d a b k hd).mp hk⟩
  · intro xs
    constructor
    · rintro ⟨d,a,b,hcode,ha,hb,ρ,hbad⟩
      obtain ⟨k,hk⟩ := tupleEnumerationSurjective d ρ
      refine ⟨k,(weak_check_decoded xs d a b k ((pairDecoderExact xs d a b).mpr ⟨hcode,ha,hb⟩)).mpr ?_⟩
      simpa [hk] using hbad
    · rintro ⟨k,hk⟩
      cases hd : decodePair xs with
      | none => simp [checkWeak,eval_pair_sim,hd] at hk
      | some pair =>
        rcases pair with ⟨d,a,b⟩
        obtain ⟨hcode,ha,hb⟩ := (pairDecoderExact xs d a b).mp hd
        exact ⟨d,a,b,hcode,ha,hb,enumTuple d k,(weak_check_decoded xs d a b k hd).mp hk⟩

theorem finiteComparisonEnumeration : Comparators.FiniteComparisonEnumeration.Target :=
  ⟨expressionDecoderExact,pairDecoderExact,evaluationCorrect,finiteEvaluationCorrect,
    tupleEnumerationSurjective,counterexampleEnumeration⟩

end LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof
