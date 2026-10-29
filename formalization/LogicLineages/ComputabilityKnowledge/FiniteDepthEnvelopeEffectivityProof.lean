module

public import LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelopeEffectivity
public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationEffectivityProof

@[expose] public section

/-! External Codex continuation: actual encoded affine-envelope computation.
The existing numerical parser supplies validation, not an assumed AST instance. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeEffectivityProof
open PositiveExpression CircuitReduction FiniteComparisonEnumeration FiniteDepthEnvelope

private theorem pr_tokenize : Primrec tokenize := by
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

private theorem token_length (e : Expr Nat) : (tokens e).length = nodeCount e := by
  induction e <;> simp [tokens,nodeCount,List.length_append, *]

private theorem token_vars_aux (e : Expr Nat) (xs : List Nat) :
    (tokens e).foldr (fun t ys => if t.1 = 1 then insertVariable t.2 ys else ys) xs =
      (rawVariables e).foldr insertVariable xs := by
  induction e generalizing xs <;> simp [tokens,rawVariables,List.foldr_append, *]

private theorem token_vars (e : Expr Nat) : tokenVariables (tokens e) = variableList e :=
  token_vars_aux e []

private theorem encode_sum (xs : List Nat) : encodeVariableSum xs = encodeExpr (variableSum xs) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change 2::1::i::encodeVariableSum xs = 2::1::i::encodeExpr (variableSum xs)
    rw [ih]

private theorem encode_scale (k : Nat) (e : Expr Nat) : encodeScale k (encodeExpr e) = encodeExpr (scale k e) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2::(encodeExpr e ++ encodeScale k (encodeExpr e)) = 2::(encodeExpr e ++ encodeExpr (scale k e))
    rw [ih]

private theorem encoded_tokens (e : Expr Nat) : tokenEnvelope (tokens e) = encodeExpr (envelope e) := by
  simp only [tokenEnvelope,token_length,token_vars,encode_sum,encode_scale,envelope,bTerm,s0]

private theorem pr_insert : Primrec (fun p : Nat × List Nat => insertVariable p.1 p.2) := by
  have hm : PrimrecPred (fun p : Nat × List Nat => p.1 ∈ p.2) :=
    (Primrec.eq.exists_mem_list.comp Primrec.snd Primrec.fst).of_eq (fun p => by simp)
  exact Primrec.ite hm Primrec.snd (Primrec.list_cons.comp Primrec.fst Primrec.snd)

private theorem pr_tokenVariables : Primrec tokenVariables := by
  unfold tokenVariables
  apply Primrec.list_foldr (h := fun (_ : List Token) (p : Token × List Nat) => if p.1.1 = 1 then insertVariable p.1.2 p.2 else p.2)
    Primrec.id (Primrec.const [])
  apply Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 1))
  · exact pr_insert.comp ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  · exact Primrec.snd.comp Primrec.snd

private theorem pr_encodeSum : Primrec encodeVariableSum := by
  unfold encodeVariableSum
  apply Primrec.list_foldr (h := fun _ p => 2::1::p.1::p.2) Primrec.id (Primrec.const [0])
  exact Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_cons.comp (Primrec.const 1)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

private theorem pr_encodeScale : Primrec (fun p : Nat × List Nat => encodeScale p.1 p.2) := by
  unfold encodeScale
  apply Primrec.nat_rec' (h := fun p q => 2::(p.2++q.2)) Primrec.fst Primrec.snd
  exact Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

private theorem pr_tokenEnvelope : Primrec tokenEnvelope :=
  pr_encodeScale.comp ((Primrec.const 4).pair
    (pr_encodeScale.comp (Primrec.list_length.pair (pr_encodeSum.comp pr_tokenVariables))))

private theorem compilerComputable : Computable (fun p : Nat × List Nat => envelopeCode p.1 p.2) := by
  have he : Computable (fun p : Nat × List Nat => evalCode p.1 p.2 []) :=
    FiniteComparisonEnumerationEffectivityProof.finiteComparisonEnumerationEffectivity.1.comp
      (Computable.fst.pair (Computable.snd.pair (Computable.const [])))
  have ht : Computable (fun p : (Nat × List Nat) × Nat => (tokenize p.1.2).map tokenEnvelope) :=
    Computable.option_map (pr_tokenize.to_comp.comp (Computable.snd.comp Computable.fst))
      (pr_tokenEnvelope.to_comp.comp Computable.snd).to₂
  exact Computable.option_bind he ht.to₂

private theorem correspondence (d : Nat) (e : Expr Nat) (hb : Bounded d e) :
    envelopeCode d (encodeExpr e) = some (encodeExpr (envelope e)) := by
  have hd := (FiniteComparisonEnumerationProof.expressionDecoderExact d (encodeExpr e) e).mpr ⟨rfl,hb⟩
  unfold envelopeCode
  rw [FiniteComparisonEnumerationProof.evaluationCorrect d (encodeExpr e) [],hd,tokenize_encode]
  simp [encoded_tokens]

private theorem rejection (d : Nat) (xs : List Nat) : envelopeCode d xs = none ↔ decodeExpr d xs = none := by
  unfold envelopeCode
  rw [FiniteComparisonEnumerationProof.evaluationCorrect d xs []]
  cases hd : decodeExpr d xs with
  | none => simp
  | some e =>
    have ht : ∃ ts, tokenize xs = some ts := by
      cases h : tokenize xs with
      | none => simp [decodeExpr,h] at hd
      | some ts => exact ⟨ts,rfl⟩
    obtain ⟨ts,ht⟩ := ht
    simp [ht]

theorem finiteDepthEnvelopeEffectivity : Comparators.FiniteDepthEnvelopeEffectivity.Target := by
  refine ⟨compilerComputable,correspondence,rejection,?_⟩
  intro d e hb
  exact (FiniteComparisonEnumerationProof.expressionDecoderExact d _ _).mpr
    ⟨rfl,(FiniteDepthEnvelopeProof.sameVariables d e).mpr hb⟩

end LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeEffectivityProof
