module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafValuesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowSyntaxAlgorithm (syntaxBits termNext termParts)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowBinderRootAlgorithm (beta betaRows)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowRootDispatchAlgorithm (fixed parts)
open NumberedWindowSingletonAlgorithm (output)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeTwo)
open NumberedWindowInternalCoverAuxSyntaxNumericProof (exact_CoverAuxSyntaxSource)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit guard exact_LiteralRootGuard ViewMatches)
open NumberedWindowInternalLiteralBetaLeafProof

private theorem unary {n : Nat} (p : Program 1) (x : Program n) (v : List.Vector Nat n) :
    evaluate (.composition p (fun _ : Fin 1 => x)) v = run p (evaluate x v) := by
  rw [evaluate,vectorOne]
  rfl

private theorem binary {n : Nat} (p : Program 2) (a b : Program n) (v : List.Vector Nat n) :
    evaluate (.composition p (![a,b] : Fin 2 → Program n)) v =
      evaluate p (evaluate a v ::ᵥ evaluate b v ::ᵥ nil) := by
  rw [evaluate,vectorTwo]
  rfl

private theorem lambdaOne (f : Nat) :
    run rawLambdaShape f = 1 ↔ ∃ t b, unpackNode f = some (2,[t,b]) := by
  rw [rawLambdaShape,nodeArity _ 2 f 2 (literalEvaluation 1 2 (f ::ᵥ nil))]
  constructor
  · rintro ⟨fs,h,len⟩
    rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨z,more⟩⟩⟩ <;> simp at len
    exact ⟨a,b,h⟩
  · rintro ⟨t,b,h⟩
    exact ⟨[t,b],h,rfl⟩

private theorem lambdaFields {f t b : Nat} (h : unpackNode f = some (2,[t,b])) :
    run (field 0) f = t ∧ run (field 1) f = b := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 2 (pack [t,b]))).2
  have first : run cellHead (pack [t,b]) = t ∧ run cellTail (pack [t,b]) = pack [b] :=
    headTailOfCell (cellAt t (pack [b]))
  have last : run cellHead (pack [b]) = b := (headTailOfCell (cellAt b (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 2 (pack [t,b]) + 1) = t ∧ _
  simp only [field,cursor,applyValue,NumberedWindowFieldAlgorithm.packNode,outer,first.1,first.2,last,and_self]

private theorem instanceIff (a b r : Nat) :
    instanceValue a b = r+1 ↔ (output a 0 b).1 = some r := by
  unfold instanceValue
  cases (output a 0 b).1 <;> simp

private def visible (q r : Nat) : Prop :=
  (syntaxBits q).1 = true ∧ (syntaxBits r).1 = true ∧
    ∃ d c f a b, unpackNode q = some (6,[d,c,f,a]) ∧
      unpackNode f = some (2,[d,b]) ∧ (output a 0 b).1 = some r

private theorem betaVisible (q r : Nat) : beta q r = true ↔ visible q r := by
  constructor
  · intro h
    unfold beta guarded at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hq,hr⟩, step⟩ := h
    refine ⟨hq,hr,?_⟩
    cases parseQ : unpackNode q with
    | none => simp [parseQ] at step
    | some qx =>
      obtain ⟨qt,qv⟩ := qx
      simp only [parseQ,Option.any_some] at step
      change (unpackNode (qv.getD 2 0)).any (betaRows r (qt,qv)) = true at step
      cases parseF : unpackNode (qv.getD 2 0) with
      | none => rw [parseF] at step; cases step
      | some fx =>
        obtain ⟨ft,fv⟩ := fx
        simp only [parseF,Option.any_some,betaRows,Bool.and_eq_true,beq_iff_eq] at step
        obtain ⟨⟨⟨rfl,rfl⟩,matched⟩,runResult⟩ := step
        have exactQ := hq
        simp only [syntaxBits,termNext,parseQ,Option.any_some] at exactQ
        rcases qv with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨a,_ | ⟨last,rest⟩⟩⟩⟩⟩ <;> simp [termParts] at exactQ
        change unpackNode f = some (2,fv) at parseF
        have fnOk : (syntaxBits f).1 = true := by
          have parts := (exact_CoverAuxSyntaxSource q d c f a parseQ).2.2
          rw [parts] at hq
          simp only [Bool.and_eq_true] at hq
          exact hq.1.2
        simp only [syntaxBits,termNext,parseF,Option.any_some] at fnOk
        rcases fv with _ | ⟨d',_ | ⟨b,_ | ⟨last,rest⟩⟩⟩ <;> simp [termParts] at fnOk
        change d = d' at matched
        subst d'
        refine ⟨d,c,f,a,b,rfl,parseF,?_⟩
        change ((output a 0 b).1).any (· == r) = true at runResult
        cases hit : (output a 0 b).1 <;> simp_all
  · rintro ⟨hq,hr,d,c,f,a,b,pq,pf,out⟩
    simp [beta,guarded,hq,hr,pq,pf,betaRows,out]

private theorem rawFields {q w r d c f a : Nat} (h : unpackNode q = some (6,[d,c,f,a])) :
    evaluate (frameSlot 0 0) (tape q w r) = d ∧
    evaluate rawFunction (tape q w r) = f ∧ evaluate (frameSlot 3 0) (tape q w r) = a := by
  simp only [rawFunction,frameSlot,atSlot]
  exact ⟨(termFields h).1,(termFields h).2.2.1,(termFields h).2.2.2⟩

private theorem betaRun (V : Program 1) (U : Program 2) (vFit : ActualRawSyntax V) (uFit : InstanceFit U)
    (q w r : Nat) : evaluate (literalBetaLeaf V U) (tape q w r) = 1 ↔ visible q r := by
  simp only [literalBetaLeaf,conjunctionOne]
  constructor
  · rintro ⟨ql,rl,shape,fn,dd,inst⟩
    rw [atSlot] at ql rl
    change evaluate V (q ::ᵥ nil) = 1 at ql
    change evaluate V (r ::ᵥ nil) = 1 at rl
    rw [vFit] at ql rl
    simp only [Bool.toNat_eq_one] at ql rl
    rw [sourceIsAux,atSlot] at shape
    obtain ⟨d,c,f,a,pq⟩ := (termOne q).1 shape
    obtain ⟨dCode,fCode,aCode⟩ := rawFields (w := w) (r := r) pq
    rw [functionShape,unary,fCode,lambdaOne] at fn
    obtain ⟨d',b,pf⟩ := fn
    obtain ⟨df,bf⟩ := lambdaFields pf
    rw [domainMatch,binary,dCode,lambdaField,unary,fCode,df,exactEqualityEvaluation] at dd
    have eq : d = d' := by split at dd <;> simp_all
    rw [← eq] at pf
    have next : evaluate nextCode (tape q w r) = r+1 := by rw [nextCode,unary]; rfl
    rw [targetMatch,binary,instanceAt,binary,aCode,lambdaField,unary,fCode,bf,uFit,
      next,exactEqualityEvaluation] at inst
    have hit : instanceValue a b = r+1 := by split at inst <;> simp_all
    exact ⟨ql,rl,d,c,f,a,b,pq,pf,(instanceIff a b r).1 hit⟩
  · rintro ⟨hq,hr,d,c,f,a,b,pq,pf,out⟩
    obtain ⟨dCode,fCode,aCode⟩ := rawFields (w := w) (r := r) pq
    obtain ⟨df,bf⟩ := lambdaFields pf
    have next : evaluate nextCode (tape q w r) = r+1 := by rw [nextCode,unary]; rfl
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [atSlot]; change evaluate V (q ::ᵥ nil) = 1; rw [vFit,hq]; rfl
    · rw [atSlot]; change evaluate V (r ::ᵥ nil) = 1; rw [vFit,hr]; rfl
    · rw [sourceIsAux,atSlot]; exact (termOne q).2 ⟨d,c,f,a,pq⟩
    · rw [functionShape,unary,fCode,lambdaOne]; exact ⟨d,b,pf⟩
    · rw [domainMatch,binary,dCode,lambdaField,unary,fCode,df,exactEqualityEvaluation,if_pos rfl]
    · rw [targetMatch,binary,instanceAt,binary,aCode,lambdaField,unary,fCode,bf,uFit,
        next,(instanceIff a b r).2 out,exactEqualityEvaluation,if_pos rfl]

attribute [local irreducible] evaluate

theorem exact_LiteralBetaLeafValue (V : Program 1) (U : Program 2)
    (vFit : ActualRawSyntax V) (uFit : InstanceFit U) (q w r : Nat) :
    evaluate (literalBetaLeaf V U) (tape q w r) = (beta q r).toNat := by
  have fits : evaluate (literalBetaLeaf V U) (tape q w r) = 1 ↔ beta q r = true :=
    (betaRun V U vFit uFit q w r).trans (betaVisible q r).symm
  have bit : evaluate (literalBetaLeaf V U) (tape q w r) = 0 ∨
      evaluate (literalBetaLeaf V U) (tape q w r) = 1 := by
    unfold literalBetaLeaf
    rw [conjunctionEvaluation]
    split <;> simp
  cases yes : beta q r with
  | false =>
    change evaluate (literalBetaLeaf V U) (tape q w r) = 0
    rcases bit with eq | eq
    · exact eq
    · exact Bool.noConfusion (yes.symm.trans (fits.mp eq))
  | true =>
    change evaluate (literalBetaLeaf V U) (tape q w r) = 1
    exact fits.mpr yes

theorem exact_LiteralBetaLeafFit (xs : Entries) (heads : List Nat) (V : Program 1) (U : Program 2)
    (vFit : ActualRawSyntax V) (uFit : InstanceFit U) (leaf : Nat → Program 3)
    (fit : LeafFit (fixed xs heads) leaf) :
    LeafFit (fixed xs heads) (withBetaLeaf V U leaf) := by
  intro tag q w r fields parsed
  unfold withBetaLeaf
  split
  · rename_i isBeta
    subst tag
    have value := exact_LiteralBetaLeafValue V U vFit uFit q w r
    rw [conjunctionEvaluation,value]
    have read := exact_LiteralRootGuard 6 0 q w r
    rw [parsed] at read
    cases fields with
    | nil =>
      have on : evaluate (guard 6 0) (tape q w r) = 1 := read.mpr ⟨[],rfl,rfl⟩
      cases h : beta q r <;> simp [on,h,parts,fixed]
    | cons a more =>
      have off : evaluate (guard 6 0) (tape q w r) ≠ 1 := by
        intro h
        obtain ⟨fs,same,len⟩ := read.mp h
        cases same
        simp at len
      simp [off,parts]
  · exact fit tag q w r fields parsed

#print axioms exact_LiteralBetaLeafValue
#print axioms exact_LiteralBetaLeafFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafNumericProof
