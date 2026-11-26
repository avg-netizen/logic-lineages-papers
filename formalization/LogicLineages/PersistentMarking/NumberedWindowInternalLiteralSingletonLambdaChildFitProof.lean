module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonTableProof
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticNodeProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowSyntax
open NumberedWindowArithmeticTermCode (encodeTerm decodeTerm)
open NumberedWindowArithmeticTermCodeChecks (exact_TermCodec)
open NumberedWindowArithmeticFields (encodeNode)
open NumberedWindowArithmeticNodeProof (nodeRound nodeBelow)
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)
open NumberedWindowArithmeticSyntaxAlgorithmChecks (exact_ExactTermArgsGuards)
open NumberedWindowArithmeticSingletonChecks (exact_ExactSingletonMatrix)
open NumberedWindowArithmeticSingletonTableProof (earlierExact)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowSingletonAlgorithm (output computed table)
open NumberedWindowShiftAlgorithm (earlier)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (depthInstanceValue DepthInstanceFit)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof (GuardedDepthInstanceFit)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambdaDispatch singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof

/-- Code order: the body field of a lambda node is a strictly smaller code. -/
theorem exact_LambdaBodyBelow (q ty b : Nat) (node : unpackNode q = some (2,[ty,b])) : b < q :=
  Nat.lt_of_lt_of_eq (nodeBelow 2 [ty,b] b (by simp))
    ((congrFun (congrFun exact_ExactTaggedNodeCodec.1 2) [ty,b]).trans (codeOfNode node).symm)

/-- Course-of-values lookup at the pushed binder. The parent's own table
holds the body's row at offset one. The only conditions are the code
order `b < q` and the offset bound `1 ≤ q`, both read from the node; no
syntax hypothesis is used. -/
theorem exact_SingletonLambdaChildLookup (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    earlier (table a d q q) b 1 = computed a d q b 1 :=
  earlierExact a d q (exact_LambdaBodyBelow q ty b node)
    (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le b) (exact_LambdaBodyBelow q ty b node)))

/-- Offset correspondence on term codes. One offset step at depth `d`
in any table with room for it is the offset-zero row at depth `d+1` in
the body's own table. The bound condition is exactly `body + 1 ≤ bound`. -/
theorem exact_SingletonBinderOffset (A body : NTerm) (d bound : Nat)
    (fits : encodeTerm body + 1 ≤ bound) :
    (computed (encodeTerm A) d bound (encodeTerm body) 1).1 =
      (computed (encodeTerm A) (d+1) (encodeTerm body) (encodeTerm body) 0).1 :=
  (exact_ExactSingletonMatrix.1 A d bound 1 body fits).trans
    (exact_ExactSingletonMatrix.1 A (d+1) (encodeTerm body) 0 body
      (Nat.le_of_eq (Nat.add_zero _))).symm

/-- With both syntax bits, the first output is the node's own
offset-zero row. -/
theorem exact_SingletonOutputOfSyntax (a c n : Nat)
    (well : (syntaxBits a).1 = true) (nWell : (syntaxBits n).1 = true) :
    (output a c n).1 = some (computed a c n n 0).1 :=
  congrArg₂ (fun x y : Bool => if (x && y) = true then some (computed a c n n 0).1 else none)
    well nWell

theorem termOfSyntax (a : Nat) (well : (syntaxBits a).1 = true) :
    ∃ A : NTerm, encodeTerm A = a := by
  have decoded : (decodeTerm a).isSome = true :=
    (congrArg Prod.fst (exact_ExactTermArgsGuards a)).symm.trans well
  cases found : decodeTerm a with
  | none => simp [found] at decoded
  | some A => exact ⟨A,(exact_TermCodec.1 a A).mp found⟩

theorem syntaxOfTerm (Q : NTerm) : (syntaxBits (encodeTerm Q)).1 = true :=
  (congrArg Prod.fst (exact_ExactTermArgsGuards (encodeTerm Q))).trans
    (congrArg Option.isSome (exact_TermCodec.2.1 Q))

theorem nodeFields (tag : Nat) (xs : List Nat) (ty b : Nat)
    (node : unpackNode (encodeNode tag xs) = some (2,[ty,b])) : tag = 2 ∧ xs = [ty,b] := by
  have seen : unpackNode (encodeNode tag xs) = some (tag,xs) :=
    (congrFun exact_ExactTaggedNodeCodec.2 (encodeNode tag xs)).symm.trans (nodeRound tag xs)
  have both : some (tag,xs) = some (2,[ty,b]) := seen.symm.trans node
  exact ⟨congrArg (fun o : Option (Nat × List Nat) => (o.map Prod.fst).getD 0) both,
    congrArg (fun o : Option (Nat × List Nat) => (o.map Prod.snd).getD []) both⟩

/-- Valid child. A term whose code reads as a lambda node has a term
as its body field. -/
theorem lambdaBodyOfNode (Q : NTerm) (ty b : Nat)
    (node : unpackNode (encodeTerm Q) = some (2,[ty,b])) :
    ∃ body : NTerm, encodeTerm body = b := by
  cases Q with
  | free σ x => exact absurd (nodeFields 0 _ ty b node).1 (by decide)
  | bound σ i => exact absurd (nodeFields 1 _ ty b node).1 (by decide)
  | lam σ body =>
    exact ⟨body,congrArg (fun l : List Nat => l.getD 1 0) (nodeFields 2 _ ty b node).2⟩
  | bottom σ => exact absurd (nodeFields 3 _ ty b node).1 (by decide)
  | ordinary f bs => exact absurd (nodeFields 4 _ ty b node).1 (by decide)
  | numbered f τ k bs es => exact absurd (nodeFields 5 _ ty b node).1 (by decide)
  | auxApp σ τ fn arg => exact absurd (nodeFields 6 _ ty b node).1 (by decide)

/-- The typed lambda case of the recursion. On a guarded lambda node,
the body is itself syntactically valid, and the original singleton
output on the body at depth `d+1` is the first coordinate of the
parent table's offset-one entry. -/
theorem exact_SingletonLambdaChildOutput (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b]))
    (well : (syntaxBits a).1 = true) (qWell : (syntaxBits q).1 = true) :
    (syntaxBits b).1 = true ∧
      (output a (d+1) b).1 = some (earlier (table a d q q) b 1).1 := by
  obtain ⟨A,rfl⟩ := termOfSyntax a well
  obtain ⟨Q,rfl⟩ := termOfSyntax q qWell
  obtain ⟨body,rfl⟩ := lambdaBodyOfNode Q ty b node
  have bWell : (syntaxBits (encodeTerm body)).1 = true := syntaxOfTerm body
  have below := exact_LambdaBodyBelow (encodeTerm Q) ty (encodeTerm body) node
  have lookup := exact_SingletonLambdaChildLookup (encodeTerm A) d (encodeTerm Q) ty
    (encodeTerm body) node
  have offset := exact_SingletonBinderOffset A body d (encodeTerm Q) below
  exact ⟨bWell,
    (exact_SingletonOutputOfSyntax (encodeTerm A) (d+1) (encodeTerm body) well bWell).trans
      (congrArg some (offset.symm.trans (congrArg Prod.fst lookup.symm)))⟩

/-- The same fallback's guarded fit supplies the child premise. -/
theorem exact_LambdaChildFitOfGuarded (U : Program 3) (uFit : GuardedDepthInstanceFit U) :
    LambdaChildFit U := by
  intro a d q ty b node well qWell
  have child := exact_SingletonLambdaChildOutput a d q ty b node well qWell
  have value : depthInstanceValue a (d+1) b = (earlier (table a d q q) b 1).1 + 1 :=
    congrArg (fun o : Option Nat => (o.map Nat.succ).getD 0) child.2
  exact (uFit a (d+1) b well child.1).trans value

/-- The written dispatch is guarded-calibrated from the fallback's
guarded fit alone, so it can itself serve as a fallback. -/
theorem exact_LiteralLambdaDispatchGuardedFitOfFallback (U : Program 3)
    (uFit : GuardedDepthInstanceFit U) :
    GuardedDepthInstanceFit (singletonLambdaDispatch U) :=
  exact_LiteralLambdaDispatchGuardedFit U uFit (exact_LambdaChildFitOfGuarded U uFit)

/-- All-input calibration of the installed lambda program with no child
hypothesis. -/
theorem exact_LiteralSingletonLambdaCalibrationOfFallback (V : Program 1) (H : Program 2)
    (U : Program 3) (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H)
    (uFit : GuardedDepthInstanceFit U) :
    DepthInstanceFit (singletonLambda V H U) :=
  exact_LiteralSingletonLambdaCalibration V H U vFit hFit uFit
    (exact_LambdaChildFitOfGuarded U uFit)

#print axioms exact_LambdaBodyBelow
#print axioms exact_SingletonLambdaChildLookup
#print axioms exact_SingletonBinderOffset
#print axioms exact_SingletonOutputOfSyntax
#print axioms termOfSyntax
#print axioms syntaxOfTerm
#print axioms nodeFields
#print axioms lambdaBodyOfNode
#print axioms exact_SingletonLambdaChildOutput
#print axioms exact_LambdaChildFitOfGuarded
#print axioms exact_LiteralLambdaDispatchGuardedFitOfFallback
#print axioms exact_LiteralSingletonLambdaCalibrationOfFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaChildFitProof
