module

public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalControlProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! Internal correctness of equality-to-one normalization. The `equalsOne`
recursion equations come from actual node/composition equations at actual
child tags; its internal biconditional and Boolean range are proved by the
calculus's own induction, using the paid internal zero test at the actual
step child. Normalized occurrences are reduced by the composition equation;
same-AST acceptance uses actual registry coherence. The published clause
builds a fresh index for the normalized S and lifts the internal range proof
into the actual D by finite axiom inclusion. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.Proof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry GorbowSubstitution
open GorbowPRDefiningEquations (call argumentVariables nodeEquations)
open GorbowPRNumeralCalculation (Theory)
open List.Vector

/-! ### External evaluation -/

private theorem stepEval (x e : Nat) :
    evaluate equalsOneStep (x ::ᵥ e ::ᵥ List.Vector.nil) =
      evaluate GorbowPRInternalControl.zeroTest (x ::ᵥ List.Vector.nil) := by
  have hv : (List.Vector.ofFn fun _ : Fin 1 =>
      evaluate (.projection (0 : Fin 2)) (x ::ᵥ e ::ᵥ List.Vector.nil)) =
      x ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    obtain rfl : i = 0 := Fin.eq_zero i
    rfl
  show evaluate GorbowPRInternalControl.zeroTest (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (0 : Fin 2)) (x ::ᵥ e ::ᵥ List.Vector.nil)) = _
  rw [hv]

private theorem evalEqualsOne : ∀ x : Nat,
    evaluate equalsOne (x ::ᵥ List.Vector.nil) = if x = 1 then 1 else 0
  | 0 => (GorbowPRProgram.Proof.recursionZero 0 .zero equalsOneStep List.Vector.nil).trans
      (by simp [evaluate])
  | x + 1 => (GorbowPRProgram.Proof.recursionSuccessor 0 .zero equalsOneStep
      List.Vector.nil x).trans
      ((stepEval x (evaluate equalsOne (x ::ᵥ List.Vector.nil))).trans
        ((GorbowPRInternalControl.Proof.actualEvaluation.1 x).trans (by simp)))

private theorem evalNormalize {n : Nat} (q : Program n) (v : List.Vector Nat n) :
    evaluate (normalize q) v = if evaluate q v = 1 then 1 else 0 := by
  have hv : (List.Vector.ofFn fun _ : Fin 1 => evaluate q v) =
      evaluate q v ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    obtain rfl : i = 0 := Fin.eq_zero i
    rfl
  show evaluate equalsOne (List.Vector.ofFn fun _ : Fin 1 => evaluate q v) = _
  rw [hv]
  exact evalEqualsOne _

theorem actualEvaluation : GorbowVerifierNormalization.Targets.ActualEvaluation :=
  ⟨evalEqualsOne, fun _ q v => evalNormalize q v⟩

/-! ### Hilbert combinators -/

private def liftK {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def compose {A : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation A (.imp b c)) (q : Derivation A (.imp a b)) : Derivation A (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftK a p)) q

private def mpUnder {A : Sentence → Prop} {n : Nat} {a x y : Formula n}
    (p : Derivation A (.imp a (.imp x y))) (q : Derivation A (.imp a x)) :
    Derivation A (.imp a y) :=
  .mp (.mp (.logical (.s a x y)) p) q

private def conjI {A : Sentence → Prop} {n : Nat} {a b : Formula n}
    (h1 : Derivation A a) (h2 : Derivation A b) : Derivation A (.conj a b) :=
  .mp (.mp (.logical (.andIntro a b)) h1) h2

private def bicondLeft {A : Sentence → Prop} {n : Nat} {P Q : Formula n}
    (h : Derivation A (GorbowBooleanTruth.biconditional P Q)) : Derivation A (.imp P Q) :=
  .mp (.logical (.andLeft (.imp P Q) (.imp Q P))) h

private def bicondRight {A : Sentence → Prop} {n : Nat} {P Q : Formula n}
    (h : Derivation A (GorbowBooleanTruth.biconditional P Q)) : Derivation A (.imp Q P) :=
  .mp (.logical (.andRight (.imp P Q) (.imp Q P))) h

private def bicondTrans {A : Sentence → Prop} {n : Nat} {P Q R : Formula n}
    (h1 : Derivation A (GorbowBooleanTruth.biconditional P Q))
    (h2 : Derivation A (GorbowBooleanTruth.biconditional Q R)) :
    Derivation A (GorbowBooleanTruth.biconditional P R) :=
  conjI (compose (bicondLeft h2) (bicondLeft h1)) (compose (bicondRight h1) (bicondRight h2))

/-! ### Equality reasoning in arbitrary contexts -/

private def shift {ctx : Nat} (t : Term ctx) : Term (ctx + 1) :=
  substitute (fun i : Fin ctx => Term.var i.succ) t

private theorem shiftInst {ctx : Nat} (a t : Term ctx) :
    substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) (shift t) = t := by
  unfold shift
  rw [substitute_composition]
  change substitute Term.var t = t
  exact substitute_variables t

private theorem instShiftEqual {ctx : Nat} (L : Term ctx) (M : Term (ctx + 1)) (a : Term ctx) :
    GorbowStandardInstances.instantiate (.equal (shift L) M) a =
      .equal L (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) M) := by
  show Formula.equal (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) (shift L))
    (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) M) = _
  rw [shiftInst]

private theorem instShiftEqualR {ctx : Nat} (M : Term (ctx + 1)) (L : Term ctx) (a : Term ctx) :
    GorbowStandardInstances.instantiate (.equal M (shift L)) a =
      .equal (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) M) L := by
  show Formula.equal (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) M)
    (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) (shift L)) = _
  rw [shiftInst]

private theorem eqTrans {A : Sentence → Prop} {ctx : Nat} {a b c : Term ctx}
    (h1 : Derivation A (.equal a b)) (h2 : Derivation A (.equal b c)) :
    Nonempty (Derivation A (.equal a c)) := by
  have e : Derivation A (.imp (.equal b c)
      (.imp (GorbowStandardInstances.instantiate (.equal (shift a) (.var 0)) b)
        (GorbowStandardInstances.instantiate (.equal (shift a) (.var 0)) c))) :=
    .logical (.equalityReplace (.equal (shift a) (.var 0)) b c)
  rw [instShiftEqual, instShiftEqual] at e
  exact ⟨.mp (.mp e h2) h1⟩

private theorem eqSymm {A : Sentence → Prop} {ctx : Nat} {a b : Term ctx}
    (h : Derivation A (.equal a b)) : Nonempty (Derivation A (.equal b a)) := by
  have e : Derivation A (.imp (.equal a b)
      (.imp (GorbowStandardInstances.instantiate (.equal (.var 0) (shift a)) a)
        (GorbowStandardInstances.instantiate (.equal (.var 0) (shift a)) b))) :=
    .logical (.equalityReplace (.equal (.var 0) (shift a)) a b)
  rw [instShiftEqualR, instShiftEqualR] at e
  exact ⟨.mp (.mp e h) (.logical (.reflexive a))⟩

/-- Equal terms have equivalent "equals one" atoms. -/
private theorem eqIffOne {A : Sentence → Prop} {ctx : Nat} {u v : Term ctx}
    (h : Derivation A (.equal u v)) :
    Nonempty (Derivation A (GorbowBooleanTruth.biconditional
      (.equal u (Term.numeral 1)) (.equal v (Term.numeral 1)))) := by
  obtain ⟨hs⟩ := eqSymm h
  have e1 : Derivation A (.imp (.equal u v)
      (.imp (.equal u (Term.numeral 1)) (.equal v (Term.numeral 1)))) :=
    .logical (.equalityReplace (.equal (.var 0) (Term.numeral 1)) u v)
  have e2 : Derivation A (.imp (.equal v u)
      (.imp (.equal v (Term.numeral 1)) (.equal u (Term.numeral 1)))) :=
    .logical (.equalityReplace (.equal (.var 0) (Term.numeral 1)) v u)
  exact ⟨conjI (.mp e1 h) (.mp e2 hs)⟩

/-- Boolean range transports along an actual equality. -/
private theorem rangeTransport {A : Sentence → Prop} {ctx : Nat} {u v : Term ctx}
    (h : Derivation A (.equal u v)) (hr : Derivation A (booleanRange v)) :
    Nonempty (Derivation A (booleanRange u)) := by
  obtain ⟨hs⟩ := eqSymm h
  have e : Derivation A (.imp (.equal v u) (.imp (booleanRange v) (booleanRange u))) :=
    .logical (.equalityReplace (booleanRange (.var 0)) v u)
  exact ⟨.mp (.mp e hs) hr⟩

/-- y = 0 iff S y = 1, by congruence and successor injectivity. -/
private theorem succIff {A : Sentence → Prop} {ctx : Nat} (y : Term ctx) :
    Nonempty (Derivation A (GorbowBooleanTruth.biconditional
      (.equal y .zero) (.equal (.succ y) (Term.numeral 1)))) := by
  have e : Derivation A (.imp (.equal y .zero)
      (.imp (GorbowStandardInstances.instantiate (.equal (shift (.succ y)) (.succ (.var 0))) y)
        (GorbowStandardInstances.instantiate (.equal (shift (.succ y)) (.succ (.var 0))) .zero))) :=
    .logical (.equalityReplace (.equal (shift (.succ y)) (.succ (.var 0))) y .zero)
  rw [instShiftEqual, instShiftEqual] at e
  have fwd : Derivation A (.imp (.equal y .zero) (.equal (.succ y) (Term.numeral 1))) :=
    mpUnder e (liftK _ (.logical (.reflexive (.succ y))))
  have bwd : Derivation A (.imp (.equal (.succ y) (Term.numeral 1)) (.equal y .zero)) :=
    .arithmetic (.succInjective y .zero)
  exact ⟨conjI fwd bwd⟩

/-! ### Node values and actual child lookups -/

private theorem sub_call {arity ctx out : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem sub_arguments {arity ctx : Nat} (args : List.Vector (Term ctx) arity) :
    (argumentVariables arity).map (substitute args.get) = args := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables, substitute]

private theorem callCong {A : Sentence → Prop} {ctx k : Nat} (tag : Nat)
    (v w : List.Vector (Term ctx) k)
    (h : ∀ i, Nonempty (Derivation A (.equal (v.get i) (w.get i)))) :
    Nonempty (Derivation A (.equal (call tag v) (call tag w))) := by
  obtain ⟨d⟩ := GorbowPRInternalCoherence.Proof.openTermCongruence A k ctx
    (call tag (argumentVariables k)) v.get w.get h
  rw [sub_call, sub_call, sub_arguments, sub_arguments] at d
  exact ⟨d⟩

private theorem zeroValue {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨0, .zero⟩) (ctx : Nat) (args : List.Vector (Term ctx) 0) :
    Nonempty (Derivation (Theory p) (.equal (call tag args) .zero)) := by
  obtain ⟨d⟩ := GorbowPRSymbolicEquations.Proof.nodeEquationInstances n p tag 0 .zero h 0 ctx
    (call tag List.Vector.nil) .zero (by simp [nodeEquations]) Fin.elim0
  rw [sub_call] at d
  rw [List.Vector.eq_nil args]
  exact ⟨d⟩

private theorem projectionValue {n m : Nat} (p : Program n) (tag : Nat) (i : Fin m)
    (h : (nodes p)[tag]? = some ⟨m, .projection i⟩) (ctx : Nat)
    (args : List.Vector (Term ctx) m) :
    Nonempty (Derivation (Theory p) (.equal (call tag args) (args.get i))) := by
  obtain ⟨d⟩ := GorbowPRSymbolicEquations.Proof.nodeEquationInstances n p tag m (.projection i) h
    m ctx (call tag (argumentVariables m)) (.var i) (by simp [nodeEquations]) args.get
  rw [sub_call, sub_arguments] at d
  exact ⟨d⟩

private theorem projectionValueAt {n m : Nat} (p : Program n) (tag : Nat) (i : Fin m)
    (h : (nodes p)[tag]? = some ⟨m, .projection i⟩) (ctx : Nat)
    (args : List.Vector (Term ctx) m) (t : Term ctx) (ht : args.get i = t) :
    Nonempty (Derivation (Theory p) (.equal (call tag args) t)) := by
  obtain ⟨d⟩ := projectionValue p tag i h ctx args
  rw [ht] at d
  exact ⟨d⟩

private theorem compFunLookup {n m k : Nat} (p : Program n) (tag : Nat) (f : Program k)
    (g : Fin k → Program m) (h : (nodes p)[tag]? = some ⟨m, .composition f g⟩) :
    (nodes p)[tag + 1]? = some ⟨k, f⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m, .composition f g⟩ 1 ⟨k, f⟩ h
    (GorbowPRChildTags.Proof.compositionFunction m k f g)

private theorem compArgLookup {n m k : Nat} (p : Program n) (tag : Nat) (f : Program k)
    (g : Fin k → Program m) (h : (nodes p)[tag]? = some ⟨m, .composition f g⟩) (i : Fin k) :
    (nodes p)[tag + GorbowPRChildTags.argumentTag f g i]? = some ⟨m, g i⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m, .composition f g⟩
    (GorbowPRChildTags.argumentTag f g i) ⟨m, g i⟩ h
    (GorbowPRChildTags.Proof.compositionArgument m k f g i)

private theorem recBaseLookup {n k : Nat} (p : Program n) (tag : Nat) (f : Program k)
    (g : Program (k + 2)) (h : (nodes p)[tag]? = some ⟨k + 1, .recursion f g⟩) :
    (nodes p)[tag + 1]? = some ⟨k, f⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨k + 1, .recursion f g⟩ 1 ⟨k, f⟩ h
    (GorbowPRChildTags.Proof.recursionBase k f g)

private theorem recStepLookup {n k : Nat} (p : Program n) (tag : Nat) (f : Program k)
    (g : Program (k + 2)) (h : (nodes p)[tag]? = some ⟨k + 1, .recursion f g⟩) :
    (nodes p)[tag + GorbowPRChildTags.stepTag f]? = some ⟨k + 2, g⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨k + 1, .recursion f g⟩
    (GorbowPRChildTags.stepTag f) ⟨k + 2, g⟩ h (GorbowPRChildTags.Proof.recursionStep k f g)

private theorem compValue {n m k : Nat} (p : Program n) (tag : Nat) (f : Program k)
    (g : Fin k → Program m) (h : (nodes p)[tag]? = some ⟨m, .composition f g⟩) (ctx : Nat)
    (args : List.Vector (Term ctx) m) (w : List.Vector (Term ctx) k)
    (hw : ∀ i, Nonempty (Derivation (Theory p)
      (.equal (call (tag + GorbowPRChildTags.argumentTag f g i) args) (w.get i)))) :
    Nonempty (Derivation (Theory p) (.equal (call tag args) (call (tag + 1) w))) := by
  obtain ⟨e⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag m k f g h ctx args
  obtain ⟨c⟩ := callCong (A := Theory p) (tag + 1)
    (List.Vector.ofFn fun i => call (tag + GorbowPRChildTags.argumentTag f g i) args) w
    (fun i => by
      simp only [List.Vector.get_ofFn]
      exact hw i)
  exact eqTrans e c

private theorem objectInduction {A : Sentence → Prop} {ctx : Nat} (φ : Formula (ctx + 1))
    (base : Derivation A (GorbowStandardInstances.instantiate φ .zero))
    (step : Derivation A (.imp φ (GorbowStandardInduction.successorInstance φ)))
    (t : Term ctx) : Nonempty (Derivation A (GorbowStandardInstances.instantiate φ t)) := by
  have ind : Derivation A (GorbowStandardInduction.inductionAxiom φ) := .arithmetic (.induction φ)
  have hall : Derivation A (.all φ) := .mp (.mp ind base) (.generalize step)
  exact ⟨.mp (.logical (.allInstantiate φ t)) hall⟩

/-! ### Raw equalsOne equations at an actual occurrence -/

private theorem eoZero {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, equalsOne⟩) (ctx : Nat) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.zero ::ᵥ List.Vector.nil : List.Vector (Term ctx) 1)) .zero)) := by
  have hb := recBaseLookup p tag (.zero : Program 0) equalsOneStep h
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 0 .zero
    equalsOneStep h ctx List.Vector.nil
  obtain ⟨z2⟩ := zeroValue p (tag + 1) hb ctx List.Vector.nil
  exact eqTrans z1 z2

private theorem eoZtLookup {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, equalsOne⟩) :
    (nodes p)[tag + GorbowPRChildTags.stepTag (.zero : Program 0) + 1]? =
      some ⟨1, GorbowPRInternalControl.zeroTest⟩ :=
  compFunLookup p (tag + GorbowPRChildTags.stepTag (.zero : Program 0))
    GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => .projection (0 : Fin 2))
    (recStepLookup p tag (.zero : Program 0) equalsOneStep h)

private theorem eoSucc {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, equalsOne⟩) (ctx : Nat) (x : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.succ x ::ᵥ List.Vector.nil))
        (call (tag + GorbowPRChildTags.stepTag (.zero : Program 0) + 1)
          (x ::ᵥ List.Vector.nil)))) := by
  have hs := recStepLookup p tag (.zero : Program 0) equalsOneStep h
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 0 .zero
    equalsOneStep h ctx x List.Vector.nil
  obtain ⟨c⟩ := compValue p (tag + GorbowPRChildTags.stepTag (.zero : Program 0))
    GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => .projection (0 : Fin 2)) hs ctx
    (x ::ᵥ call tag (x ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) (x ::ᵥ List.Vector.nil)
    (fun i => by
      obtain rfl : i = 0 := Fin.eq_zero i
      exact projectionValueAt p _ (0 : Fin 2)
        (compArgLookup p (tag + GorbowPRChildTags.stepTag (.zero : Program 0))
          GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => .projection (0 : Fin 2)) hs 0)
        ctx _ _ (by first | rfl | simp))
  exact eqTrans s1 c

/-! ### Internal equalsOne by object induction -/

private def eoFormula {ctx : Nat} (tag : Nat) : Formula (ctx + 1) :=
  GorbowBooleanTruth.biconditional
    (.equal (call tag (Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))
    (.equal (Term.var 0) (Term.numeral 1))

private theorem eoInst {ctx : Nat} (tag : Nat) (t : Term ctx) :
    GorbowStandardInstances.instantiate (eoFormula (ctx := ctx) tag) t =
      GorbowBooleanTruth.biconditional
        (.equal (call tag (t ::ᵥ List.Vector.nil)) (Term.numeral 1))
        (.equal t (Term.numeral 1)) := by
  unfold GorbowStandardInstances.instantiate eoFormula GorbowBooleanTruth.biconditional
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem eoSuccInst {ctx : Nat} (tag : Nat) :
    GorbowStandardInduction.successorInstance (eoFormula (ctx := ctx) tag) =
      GorbowBooleanTruth.biconditional
        (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) (Term.numeral 1))
        (.equal (Term.succ (Term.var 0)) (Term.numeral 1)) := by
  unfold GorbowStandardInduction.successorInstance eoFormula GorbowBooleanTruth.biconditional
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem eoCore {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, equalsOne⟩) (ctx : Nat) (x : Term ctx) :
    Nonempty (Derivation (Theory p) (GorbowBooleanTruth.biconditional
      (.equal (call tag (x ::ᵥ List.Vector.nil)) (Term.numeral 1))
      (.equal x (Term.numeral 1)))) := by
  obtain ⟨z0⟩ := eoZero p tag h ctx
  obtain ⟨b0⟩ := eqIffOne z0
  obtain ⟨s⟩ := eoSucc p tag h (ctx + 1) (.var 0)
  obtain ⟨s'⟩ := eqIffOne s
  obtain ⟨zt⟩ := GorbowPRInternalControl.Proof.internalZeroTest n p
    (tag + GorbowPRChildTags.stepTag (.zero : Program 0) + 1) (eoZtLookup p tag h) (ctx + 1)
    (.var 0)
  obtain ⟨si⟩ := succIff (A := Theory p) (Term.var 0 : Term (ctx + 1))
  have stepBody : Derivation (Theory p) (GorbowBooleanTruth.biconditional
      (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) (Term.numeral 1))
      (.equal (Term.succ (Term.var 0)) (Term.numeral 1))) :=
    bicondTrans (bicondTrans s' zt) si
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (eoFormula (ctx := ctx) tag) .zero) := by
    rw [eoInst]
    exact b0
  have step : Derivation (Theory p) (.imp (eoFormula (ctx := ctx) tag)
      (GorbowStandardInduction.successorInstance (eoFormula (ctx := ctx) tag))) := by
    rw [eoSuccInst]
    exact liftK _ stepBody
  obtain ⟨d⟩ := objectInduction (eoFormula (ctx := ctx) tag) base step x
  rw [eoInst] at d
  exact ⟨d⟩

theorem internalEqualsOne : GorbowVerifierNormalization.Targets.InternalEqualsOne := by
  intro n p tag h ctx x
  exact eoCore p tag h ctx x

/-! ### Internal equalsOne Boolean range by object induction -/

private def eoRangeFormula {ctx : Nat} (tag : Nat) : Formula (ctx + 1) :=
  booleanRange (call tag (Term.var 0 ::ᵥ List.Vector.nil))

private theorem rangeInst {ctx : Nat} (tag : Nat) (t : Term ctx) :
    GorbowStandardInstances.instantiate (eoRangeFormula (ctx := ctx) tag) t =
      booleanRange (call tag (t ::ᵥ List.Vector.nil)) := by
  unfold GorbowStandardInstances.instantiate eoRangeFormula booleanRange
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem rangeSuccInst {ctx : Nat} (tag : Nat) :
    GorbowStandardInduction.successorInstance (eoRangeFormula (ctx := ctx) tag) =
      booleanRange (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) := by
  unfold GorbowStandardInduction.successorInstance eoRangeFormula booleanRange
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem eoRange {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, equalsOne⟩) (ctx : Nat) (x : Term ctx) :
    Nonempty (Derivation (Theory p) (booleanRange (call tag (x ::ᵥ List.Vector.nil)))) := by
  obtain ⟨z0⟩ := eoZero p tag h ctx
  obtain ⟨s⟩ := eoSucc p tag h (ctx + 1) (.var 0)
  obtain ⟨zr⟩ := GorbowPRInternalControl.Proof.internalBooleanRange n p
    (tag + GorbowPRChildTags.stepTag (.zero : Program 0) + 1) (eoZtLookup p tag h) (ctx + 1)
    (.var 0)
  obtain ⟨sr⟩ := rangeTransport s zr
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (eoRangeFormula (ctx := ctx) tag) .zero) := by
    rw [rangeInst]
    exact .mp (.logical (.orLeft _ _)) z0
  have step : Derivation (Theory p) (.imp (eoRangeFormula (ctx := ctx) tag)
      (GorbowStandardInduction.successorInstance (eoRangeFormula (ctx := ctx) tag))) := by
    rw [rangeSuccInst]
    exact liftK _ sr
  obtain ⟨d⟩ := objectInduction (eoRangeFormula (ctx := ctx) tag) base step x
  rw [rangeInst] at d
  exact ⟨d⟩

/-! ### Normalized occurrences -/

/-- A normalized occurrence equals `equalsOne` applied to its actual q child call. -/
private theorem normalizeValue {n m : Nat} (q : Program n) (p : Program m) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨n, normalize q⟩) (ctx : Nat)
    (args : List.Vector (Term ctx) n) :
    Nonempty (Derivation (Theory p) (.equal (call tag args)
      (call (tag + 1) (call (tag + GorbowPRChildTags.argumentTag equalsOne
        (fun _ : Fin 1 => q) 0) args ::ᵥ List.Vector.nil)))) :=
  compValue p tag equalsOne (fun _ : Fin 1 => q) h ctx args
    (call (tag + GorbowPRChildTags.argumentTag equalsOne (fun _ : Fin 1 => q) 0) args ::ᵥ
      List.Vector.nil)
    (fun i => by
      obtain rfl : i = 0 := Fin.eq_zero i
      exact ⟨.logical (.reflexive _)⟩)

theorem internalNormalizedRange : GorbowVerifierNormalization.Targets.InternalNormalizedRange := by
  intro n q m p tag h ctx args
  have hf := compFunLookup p tag equalsOne (fun _ : Fin 1 => q) h
  obtain ⟨c⟩ := normalizeValue q p tag h ctx args
  obtain ⟨r⟩ := eoRange p (tag + 1) hf ctx
    (call (tag + GorbowPRChildTags.argumentTag equalsOne (fun _ : Fin 1 => q) 0) args)
  exact rangeTransport c r

theorem internalSameASTAcceptance :
    GorbowVerifierNormalization.Targets.InternalSameASTAcceptance := by
  intro n q m p normalizedTag originalTag hN hO ctx args
  have hf := compFunLookup p normalizedTag equalsOne (fun _ : Fin 1 => q) hN
  have hq := compArgLookup p normalizedTag equalsOne (fun _ : Fin 1 => q) hN 0
  obtain ⟨c⟩ := normalizeValue q p normalizedTag hN ctx args
  obtain ⟨b1⟩ := eqIffOne c
  obtain ⟨b2⟩ := eoCore p (normalizedTag + 1) hf ctx
    (call (normalizedTag + GorbowPRChildTags.argumentTag equalsOne (fun _ : Fin 1 => q) 0) args)
  obtain ⟨co⟩ := GorbowPRInternalCoherence.Proof.registryCoherence m p
    (normalizedTag + GorbowPRChildTags.argumentTag equalsOne (fun _ : Fin 1 => q) 0) originalTag
    n q hq hO ctx args
  obtain ⟨b3⟩ := eqIffOne co
  exact ⟨bicondTrans (bicondTrans b1 b2) b3⟩

/-! ### The normalized actual universal verifier in the published D -/

theorem publishedBooleanVerifier :
    GorbowVerifierNormalization.Targets.PublishedBooleanVerifier := by
  intro pF pR q c hA
  obtain ⟨hcal, hq, _⟩ := hA
  have hUV : GorbowPublishedDCB.UniversalVerifier (normalize q) := by
    intro c' fuel k formula cert
    rw [evalNormalize, hq c' fuel k formula cert]
    cases GorbowEnumeratedProvability.check (c', fuel) k formula cert <;> simp
  obtain ⟨cNew, hcNew⟩ := (GorbowPublishedDCB.Proof.finiteSPresentation pF pR (normalize q)).2
  refine ⟨cNew, ⟨hcal, hUV, hcNew⟩, fun ctx args => ?_⟩
  have hl := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (normalize q)
  obtain ⟨d⟩ := internalNormalizedRange 5 q _ _ (GorbowNamedInternalProvability.checkerTag pF)
    hl ctx args
  exact GorbowTheoryProofProof.monotonicity _ (GorbowPublishedDCB.D pF pR (normalize q) cNew)
    (fun σ h => Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))))
    ctx _ ⟨d⟩

theorem fullTarget : GorbowVerifierNormalization.Targets.Target :=
  ⟨actualEvaluation, internalEqualsOne, internalNormalizedRange, internalSameASTAcceptance,
    publishedBooleanVerifier⟩

end LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.Proof
