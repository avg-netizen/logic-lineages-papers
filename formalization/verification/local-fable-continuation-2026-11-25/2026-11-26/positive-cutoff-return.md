The correspondence is not present as a standalone statement. It exists only inside the private `child` lemma and the `.lam` case of `NumberedWindowShiftProof.term`. The module below is the smallest exported bridge I can state, composed entirely from existing lemmas. It adds no program, and nothing is compiled or written.

## Where the bridge comes from

- **Table lookup:** `NumberedWindowShiftTableProof.earlierExact`, with side conditions `code < n` and `offset ≤ bound`.
- **Offset-to-cutoff exchange:** `NumberedWindowShiftChecks.exact_ShiftMatrix.1`, with side condition `encodeTerm Q + offset ≤ bound`.
- **Actual output:** `exact_ShiftOutput` and `exact_TermCodec.2.1`.
- **Actual bounds:** the top-level call on code `n` uses `table m c n n`, so the bound is `n` itself. For a lambda node, `nodeBelow` gives `encodeTerm q < n`, which supplies both `1 ≤ n` and `encodeTerm q + 1 ≤ n`.
- **Singleton analogue:** `ExactSingletonMatrix` has the same shape (`depth + offset`), again only at matrix level.

## Module

`LogicLineages/PersistentMarking/NumberedWindowShiftLambdaBodyProof.lean`

```lean
module
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowShiftChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowShiftLambdaBodyProof
open NumberedWindowShiftAlgorithm NumberedWindowShiftTableProof
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticFields
open NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowShiftChecks (exact_ShiftMatrix exact_ShiftOutput)
open NumberedWindowArithmeticTermCodeChecks (exact_TermCodec)
open NumberedWindowArithmeticSyntaxAlgorithmChecks (exact_ExactTermArgsGuards)
open NumberedWindowArithmeticSyntaxAlgorithmTargets (OriginalRow)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)

/-- The bridge. In the actual table of the top-level call on a lambda
node, the entry read by the tag-2 row (the body code at offset one) is
the actual shift output on that body at the incremented cutoff. The
table bound is the node code itself; both side conditions come from the
body being a field of the node. -/
theorem exact_ShiftLambdaBodyEarlier (m c : Nat) (t : _) (q : NTerm) :
    (earlier (table m c (encodeTerm (NTerm.lam t q)) (encodeTerm (NTerm.lam t q)))
      (encodeTerm q) 1).1 = ((output m (c+1) (encodeTerm q)).1).getD 0 := by
  have below : encodeTerm q < encodeTerm (NTerm.lam t q) :=
    nodeBelow 2 [encodeTy t,encodeTerm q] (encodeTerm q) (by simp)
  have one : 1 ≤ encodeTerm (NTerm.lam t q) := by omega
  have fits : encodeTerm q + 1 ≤ encodeTerm (NTerm.lam t q) := by omega
  have out := exact_ShiftOutput m (c+1) (encodeTerm q)
  rw [exact_TermCodec.2.1 q] at out
  rw [earlierExact m c (encodeTerm (NTerm.lam t q)) below one,
    exact_ShiftMatrix.1 m c (encodeTerm (NTerm.lam t q)) 1 q fits]
  simp only [out,Option.map_some,Option.getD_some]

/-- The lambda row of the actual output at an arbitrary cutoff, with the
child written as the actual output on the body. -/
theorem exact_ShiftOutputLambda (m c : Nat) (t : _) (q : NTerm) :
    (output m c (encodeTerm (NTerm.lam t q))).1 =
      some (packNode 2 [encodeTy t,((output m (c+1) (encodeTerm q)).1).getD 0]) := by
  have body := exact_ShiftOutput m (c+1) (encodeTerm q)
  rw [exact_TermCodec.2.1 q] at body
  have node := exact_ShiftOutput m c (encodeTerm (NTerm.lam t q))
  rw [exact_TermCodec.2.1 (NTerm.lam t q)] at node
  rw [node,body,← encodePack]
  simp only [Option.map_some,Option.getD_some,shift,encodeTerm]

/-- A syntactically valid code with the literal tag-2 shape decodes to a
lambda whose type and body codes are the two stored fields. -/
theorem exact_DecodedLambdaOfShape (n ty b : Nat) (well : (syntaxBits n).1 = true)
    (shaped : unpackNode n = some (2,[ty,b])) :
    ∃ t q, decodeTerm n = some (NTerm.lam t q) ∧ encodeTy t = ty ∧ encodeTerm q = b := by
  rw [exact_ExactTermArgsGuards n] at well
  change (decodeTerm n).isSome = true at well
  cases found : decodeTerm n with
  | none => simp [found] at well
  | some Q =>
    have code : encodeTerm Q = n := (exact_TermCodec.1 n Q).mp found
    have view : ∀ k fs, encodeNode k fs = n → (k,fs) = (2,[ty,b]) := by
      intro k fs h
      have packed : unpackNode n = some (k,fs) := by
        rw [← h,encodePack]
        exact nodePacked k fs
      rw [shaped] at packed
      exact (Option.some.inj packed).symm
    cases Q with
    | lam t q =>
      have same := view 2 [encodeTy t,encodeTerm q] code
      simp at same
      exact ⟨t,q,found,same.1,same.2⟩
    | free σ x =>
      have same := view 0 [encodeTy σ,x] code
      simp at same
    | bound σ i =>
      have same := view 1 [encodeTy σ,i] code
      simp at same
    | bottom σ =>
      have same := view 3 [encodeTy σ] code
      simp at same
    | ordinary f bs =>
      have same := view 4 [encodeHead f,encodeArgs bs] code
      simp at same
    | numbered f τ k bs es =>
      have same := view 5 [encodeHead f,encodeTy τ,k,encodeArgs bs,encodeArgs es] code
      simp at same
    | auxApp σ τ p u =>
      have same := view 6 [encodeTy σ,encodeTy τ,encodeTerm p,encodeTerm u] code
      simp at same

/-- Raw-code form for the two source guards. On a valid code of literal
lambda shape: the body is itself valid, the table entry read by the row
is the actual output on the body at cutoff plus one, and the node's
output is the rebuilt lambda around it. -/
theorem exact_ShiftLambdaRowValue (m c n ty b : Nat) (well : (syntaxBits n).1 = true)
    (shaped : unpackNode n = some (2,[ty,b])) :
    (syntaxBits b).1 = true ∧
    (earlier (table m c n n) b 1).1 = ((output m (c+1) b).1).getD 0 ∧
    ((output m c n).1).getD 0 = packNode 2 [ty,((output m (c+1) b).1).getD 0] := by
  obtain ⟨t,q,decoded,rfl,rfl⟩ := exact_DecodedLambdaOfShape n ty b well shaped
  obtain rfl := (exact_TermCodec.1 n (NTerm.lam t q)).mp decoded
  refine ⟨?_,exact_ShiftLambdaBodyEarlier m c t q,?_⟩
  · rw [exact_ExactTermArgsGuards (encodeTerm q)]
    change (decodeTerm (encodeTerm q)).isSome = true
    simp only [exact_TermCodec.2.1 q,Option.isSome_some]
  · rw [exact_ShiftOutputLambda m c t q,Option.getD_some]

#print axioms exact_ShiftLambdaBodyEarlier
#print axioms exact_ShiftOutputLambda
#print axioms exact_DecodedLambdaOfShape
#print axioms exact_ShiftLambdaRowValue
end LogicLineages.PersistentMarking.NumberedWindowShiftLambdaBodyProof
```

## Direct application

`exact_ShiftLambdaRowValue` is the numeric input the lambda-row target from last turn needs. With `shiftCutValue m c n = ((output m c n).1).getD 0 + 1`, its third conjunct reads

`shiftCutValue m c n = packNode 2 [ty, shiftCutValue m (c+1) b - 1] + 1`

for every valid `n` of lambda shape. Its first conjunct confirms a point I flagged as an assumption last turn: a valid lambda code has a valid body. So the child call is itself behind the guard, and its value is successor-shaped and nonzero.

What `ShiftCutLambdaRowFit` still needs after this is only program evaluation, not table reasoning:
- the two field reads on a tag-2 node (`evalLiteralLambdaFields` already gives them);
- evaluation of `lambdaChild`, `predecessor` and the three `consOf` layers of `lambdaRebuilt`;
- the lambda shape bit and the `V` bit.

**Unverified points:**
- The seven `simp at same` steps in `exact_DecodedLambdaOfShape` rely on `simp` splitting the pair and list equalities and refuting the tag mismatch; this is the least mechanical part.
- `view k fs code` needs `encodeTerm` applied to a constructor to unfold to `encodeNode k fs` during unification.
- `simp only [… ,shift,encodeTerm]` in `exact_ShiftOutputLambda` uses the equation lemmas of the mutual definitions, as `NumberedWindowShiftProof.term` does.
- I inferred that `encodeTy` and `encodeHead` are reachable through the namespaces `NumberedWindowShiftProof` opens; I did not open their defining files.
