module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalControlTargets
public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
/-! Internal correctness of the literal zero-test and conditional ASTs. The
raw recursion equations come from the actual node and composition equations
at actual child tags. Each internal clause is proved by the calculus's own
induction instance on a symbolic variable, then instantiated at the arbitrary
argument; the successor branch uses `succNotZero` and the paid closed numeral
inequality, moved to the open context by actual closed-proof lifting.
Only S/K/contraposition and the existing axiom instances are used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.Proof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry GorbowSubstitution
open GorbowPRDefiningEquations (call argumentVariables nodeEquations)
open GorbowPRNumeralCalculation (Theory)
open List.Vector

/-! ### External evaluation -/

private theorem evalOne : evaluate one (List.Vector.nil : List.Vector Nat 0) = 1 := by
  have hv : (List.Vector.ofFn fun _ : Fin 1 =>
      evaluate (.zero : Program 0) (List.Vector.nil : List.Vector Nat 0)) =
      (0 : Nat) ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    obtain rfl : i = 0 := Fin.eq_zero i
    rfl
  show Nat.succ (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.zero : Program 0) (List.Vector.nil : List.Vector Nat 0)).head = Nat.succ 0
  rw [hv, List.Vector.head_cons]

private theorem evalZeroTest : ∀ x : Nat,
    evaluate zeroTest (x ::ᵥ List.Vector.nil) = if x = 0 then 1 else 0
  | 0 => (GorbowPRProgram.Proof.recursionZero 0 one zeroStep List.Vector.nil).trans
      (evalOne.trans (by simp))
  | x + 1 => (GorbowPRProgram.Proof.recursionSuccessor 0 one zeroStep List.Vector.nil x).trans
      (by simp [zeroStep, evaluate])

private theorem evalConditional : ∀ x a b : Nat,
    evaluate conditional (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) = if x = 0 then a else b
  | 0, a, b => (GorbowPRProgram.Proof.recursionZero 2 (.projection (0 : Fin 2))
      (.projection (3 : Fin 4)) (a ::ᵥ b ::ᵥ List.Vector.nil)).trans
      (by first | rfl | simp [evaluate])
  | x + 1, a, b => (GorbowPRProgram.Proof.recursionSuccessor 2 (.projection (0 : Fin 2))
      (.projection (3 : Fin 4)) (a ::ᵥ b ::ᵥ List.Vector.nil) x).trans
      (by first | rfl | simp [evaluate])

theorem actualEvaluation : GorbowPRInternalControl.Targets.ActualEvaluation :=
  ⟨evalZeroTest, evalConditional⟩

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

/-- From a proof of ¬P, the implication P → Q. -/
private def negImp {A : Sentence → Prop} {n : Nat} {P : Formula n}
    (hn : Derivation A (.neg P)) (Q : Formula n) : Derivation A (.imp P Q) :=
  .mp (.logical (.classicalContraposition Q P)) (liftK (.neg Q) hn)

/-- From a proof of P, the implication ¬P → Q. -/
private def posNegImp {A : Sentence → Prop} {n : Nat} {P : Formula n}
    (hp : Derivation A P) (Q : Formula n) : Derivation A (.imp (.neg P) Q) :=
  mpUnder (compose (.logical (.classicalContraposition Q P)) (.logical (.k (.neg P) (.neg Q))))
    (liftK (.neg P) hp)

/-! ### Equality reasoning in arbitrary contexts -/

private def shift {ctx : Nat} (t : Term ctx) : Term (ctx + 1) :=
  substitute (fun i : Fin ctx => Term.var i.succ) t

private theorem shiftInst {ctx : Nat} (a t : Term ctx) :
    substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) (shift t) = t := by
  unfold shift
  rw [substitute_composition]
  change substitute Term.var t = t
  exact substitute_variables t

private theorem shiftSucc {ctx : Nat} (t : Term ctx) :
    substitute (Fin.cases (Term.succ (Term.var 0)) (fun i : Fin ctx => Term.var i.succ) :
      Fin (ctx + 1) → Term (ctx + 1)) (shift t) = shift t :=
  substitute_composition (fun i : Fin ctx => (Term.var i.succ : Term (ctx + 1))) _ t

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

/-- The closed paid inequality ¬(0 = 1), actually lifted to any context. -/
private theorem negZeroOne (A : Sentence → Prop) (ctx : Nat) :
    Nonempty (Derivation (n := ctx) A (.neg (.equal .zero (Term.numeral 1)))) := by
  obtain ⟨c⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals A 0 1 (by decide)
  obtain ⟨l⟩ := GorbowDerivationSubstitution.Proof.closedLifting A _ ⟨c⟩ ctx
  exact ⟨l⟩

/-- From u = 0 and ¬(0 = 1), the actual equality replacement gives ¬(u = 1). -/
private theorem negTransport {A : Sentence → Prop} {ctx : Nat} {u : Term ctx}
    (hz : Derivation A (.equal u .zero))
    (hn : Derivation (n := ctx) A (.neg (.equal .zero (Term.numeral 1)))) :
    Nonempty (Derivation A (.neg (.equal u (Term.numeral 1)))) := by
  obtain ⟨hs⟩ := eqSymm hz
  have e : Derivation A (.imp (.equal .zero u)
      (.imp (.neg (.equal .zero (Term.numeral 1))) (.neg (.equal u (Term.numeral 1))))) :=
    .logical (.equalityReplace (.neg (.equal (.var 0) (Term.numeral 1))) .zero u)
  exact ⟨.mp (.mp e hs) hn⟩

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

private theorem succValue {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, .succ⟩) (ctx : Nat) (args : List.Vector (Term ctx) 1) :
    Nonempty (Derivation (Theory p) (.equal (call tag args) (.succ (args.get 0)))) := by
  obtain ⟨d⟩ := GorbowPRSymbolicEquations.Proof.nodeEquationInstances n p tag 1 .succ h 1 ctx
    (call tag (argumentVariables 1)) (.succ (.var 0)) (by simp [nodeEquations]) args.get
  rw [sub_call, sub_arguments] at d
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

/-! ### Raw recursion equations at actual occurrences -/

private theorem zeroTestZero {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, zeroTest⟩) (ctx : Nat) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.zero ::ᵥ List.Vector.nil : List.Vector (Term ctx) 1))
        (Term.numeral 1))) := by
  have hb := recBaseLookup p tag one zeroStep h
  have hf := compFunLookup p (tag + 1) .succ (fun _ : Fin 1 => (.zero : Program 0)) hb
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 0 one zeroStep h
    ctx List.Vector.nil
  obtain ⟨c⟩ := compValue p (tag + 1) .succ (fun _ : Fin 1 => (.zero : Program 0)) hb ctx
    List.Vector.nil (Term.zero ::ᵥ List.Vector.nil)
    (fun i => by
      obtain rfl : i = 0 := Fin.eq_zero i
      exact zeroValue p _
        (compArgLookup p (tag + 1) .succ (fun _ : Fin 1 => (.zero : Program 0)) hb 0) ctx
        List.Vector.nil)
  obtain ⟨s⟩ := succValue p (tag + 1 + 1) hf ctx (Term.zero ::ᵥ List.Vector.nil)
  obtain ⟨t1⟩ := eqTrans z1 c
  exact eqTrans t1 s

private theorem zeroTestSucc {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨1, zeroTest⟩) (ctx : Nat) (x : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.succ x ::ᵥ List.Vector.nil)) .zero)) := by
  have hs := recStepLookup p tag one zeroStep h
  have hf := compFunLookup p (tag + GorbowPRChildTags.stepTag one) .zero
    (Fin.elim0 : Fin 0 → Program 2) hs
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 0 one zeroStep
    h ctx x List.Vector.nil
  obtain ⟨c⟩ := compValue p (tag + GorbowPRChildTags.stepTag one) .zero
    (Fin.elim0 : Fin 0 → Program 2) hs ctx
    (x ::ᵥ call tag (x ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) List.Vector.nil
    (fun i => Fin.elim0 i)
  obtain ⟨z⟩ := zeroValue p (tag + GorbowPRChildTags.stepTag one + 1) hf ctx List.Vector.nil
  obtain ⟨t1⟩ := eqTrans s1 c
  exact eqTrans t1 z

private theorem conditionalZero {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨3, conditional⟩) (ctx : Nat) (a b : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.zero ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) a)) := by
  have hb := recBaseLookup p tag (.projection (0 : Fin 2)) (.projection (3 : Fin 4)) h
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 2
    (.projection (0 : Fin 2)) (.projection (3 : Fin 4)) h ctx (a ::ᵥ b ::ᵥ List.Vector.nil)
  obtain ⟨z2⟩ := projectionValueAt p (tag + 1) (0 : Fin 2) hb ctx
    (a ::ᵥ b ::ᵥ List.Vector.nil) a (by first | rfl | simp)
  exact eqTrans z1 z2

private theorem conditionalSucc {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨3, conditional⟩) (ctx : Nat) (x a b : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (Term.succ x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) b)) := by
  have hs := recStepLookup p tag (.projection (0 : Fin 2)) (.projection (3 : Fin 4)) h
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 2
    (.projection (0 : Fin 2)) (.projection (3 : Fin 4)) h ctx x (a ::ᵥ b ::ᵥ List.Vector.nil)
  obtain ⟨s2⟩ := projectionValueAt p (tag + GorbowPRChildTags.stepTag (.projection (0 : Fin 2)))
    (3 : Fin 4) hs ctx
    (x ::ᵥ call tag (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) b
    (by first | rfl | simp)
  exact eqTrans s1 s2

/-! ### Object induction -/

private theorem objectInduction {A : Sentence → Prop} {ctx : Nat} (φ : Formula (ctx + 1))
    (base : Derivation A (GorbowStandardInstances.instantiate φ .zero))
    (step : Derivation A (.imp φ (GorbowStandardInduction.successorInstance φ)))
    (t : Term ctx) : Nonempty (Derivation A (GorbowStandardInstances.instantiate φ t)) := by
  have ind : Derivation A (GorbowStandardInduction.inductionAxiom φ) := .arithmetic (.induction φ)
  have hall : Derivation A (.all φ) := .mp (.mp ind base) (.generalize step)
  exact ⟨.mp (.logical (.allInstantiate φ t)) hall⟩

/-! ### Internal zero test -/

private def ztFormula {ctx : Nat} (tag : Nat) : Formula (ctx + 1) :=
  GorbowBooleanTruth.biconditional
    (.equal (call tag (Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))
    (.equal (Term.var 0) .zero)

private theorem ztInst {ctx : Nat} (tag : Nat) (t : Term ctx) :
    GorbowStandardInstances.instantiate (ztFormula (ctx := ctx) tag) t =
      GorbowBooleanTruth.biconditional
        (.equal (call tag (t ::ᵥ List.Vector.nil)) (Term.numeral 1)) (.equal t .zero) := by
  unfold GorbowStandardInstances.instantiate ztFormula GorbowBooleanTruth.biconditional
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem ztSuccInst {ctx : Nat} (tag : Nat) :
    GorbowStandardInduction.successorInstance (ztFormula (ctx := ctx) tag) =
      GorbowBooleanTruth.biconditional
        (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) (Term.numeral 1))
        (.equal (Term.succ (Term.var 0)) .zero) := by
  unfold GorbowStandardInduction.successorInstance ztFormula GorbowBooleanTruth.biconditional
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

theorem internalZeroTest : GorbowPRInternalControl.Targets.InternalZeroTest := by
  intro n p tag h ctx x
  obtain ⟨z0⟩ := zeroTestZero p tag h ctx
  obtain ⟨zS⟩ := zeroTestSucc p tag h (ctx + 1) (.var 0)
  obtain ⟨n01⟩ := negZeroOne (Theory p) (ctx + 1)
  obtain ⟨nc⟩ := negTransport zS n01
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (ztFormula (ctx := ctx) tag) .zero) := by
    rw [ztInst]
    exact conjI (liftK _ (.logical (.reflexive .zero))) (liftK _ z0)
  have stepBody : Derivation (Theory p) (GorbowBooleanTruth.biconditional
      (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) (Term.numeral 1))
      (.equal (Term.succ (Term.var 0)) .zero)) :=
    conjI (negImp nc _) (negImp (.arithmetic (.succNotZero (.var 0))) _)
  have step : Derivation (Theory p) (.imp (ztFormula (ctx := ctx) tag)
      (GorbowStandardInduction.successorInstance (ztFormula (ctx := ctx) tag))) := by
    rw [ztSuccInst]
    exact liftK _ stepBody
  obtain ⟨d⟩ := objectInduction (ztFormula (ctx := ctx) tag) base step x
  rw [ztInst] at d
  exact ⟨d⟩

/-! ### Internal Boolean range -/

private def rangeFormula {ctx : Nat} (tag : Nat) : Formula (ctx + 1) :=
  .disj (.equal (call tag (Term.var 0 ::ᵥ List.Vector.nil)) .zero)
    (.equal (call tag (Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))

private theorem rangeInst {ctx : Nat} (tag : Nat) (t : Term ctx) :
    GorbowStandardInstances.instantiate (rangeFormula (ctx := ctx) tag) t =
      .disj (.equal (call tag (t ::ᵥ List.Vector.nil)) .zero)
        (.equal (call tag (t ::ᵥ List.Vector.nil)) (Term.numeral 1)) := by
  unfold GorbowStandardInstances.instantiate rangeFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

private theorem rangeSuccInst {ctx : Nat} (tag : Nat) :
    GorbowStandardInduction.successorInstance (rangeFormula (ctx := ctx) tag) =
      .disj (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) .zero)
        (.equal (call tag (Term.succ (Term.var 0) ::ᵥ List.Vector.nil)) (Term.numeral 1)) := by
  unfold GorbowStandardInduction.successorInstance rangeFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil] <;> rfl

theorem internalBooleanRange : GorbowPRInternalControl.Targets.InternalBooleanRange := by
  intro n p tag h ctx x
  obtain ⟨z0⟩ := zeroTestZero p tag h ctx
  obtain ⟨zS⟩ := zeroTestSucc p tag h (ctx + 1) (.var 0)
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (rangeFormula (ctx := ctx) tag) .zero) := by
    rw [rangeInst]
    exact .mp (.logical (.orRight _ _)) z0
  have step : Derivation (Theory p) (.imp (rangeFormula (ctx := ctx) tag)
      (GorbowStandardInduction.successorInstance (rangeFormula (ctx := ctx) tag))) := by
    rw [rangeSuccInst]
    exact liftK _ (.mp (.logical (.orLeft _ _)) zS)
  obtain ⟨d⟩ := objectInduction (rangeFormula (ctx := ctx) tag) base step x
  rw [rangeInst] at d
  exact ⟨d⟩

/-! ### Internal conditional -/

private def condFormula {ctx : Nat} (tag : Nat) (a b : Term ctx) : Formula (ctx + 1) :=
  .conj
    (.imp (.equal (Term.var 0) .zero)
      (.equal (call tag (Term.var 0 ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil)) (shift a)))
    (.imp (.neg (.equal (Term.var 0) .zero))
      (.equal (call tag (Term.var 0 ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil)) (shift b)))

private theorem condInst {ctx : Nat} (tag : Nat) (a b t : Term ctx) :
    GorbowStandardInstances.instantiate (condFormula tag a b) t =
      .conj
        (.imp (.equal t .zero) (.equal (call tag (t ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) a))
        (.imp (.neg (.equal t .zero))
          (.equal (call tag (t ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) b)) := by
  unfold GorbowStandardInstances.instantiate condFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftInst] <;> rfl

private theorem condSuccInst {ctx : Nat} (tag : Nat) (a b : Term ctx) :
    GorbowStandardInduction.successorInstance (condFormula tag a b) =
      .conj
        (.imp (.equal (Term.succ (Term.var 0)) .zero)
          (.equal (call tag (Term.succ (Term.var 0) ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil))
            (shift a)))
        (.imp (.neg (.equal (Term.succ (Term.var 0)) .zero))
          (.equal (call tag (Term.succ (Term.var 0) ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil))
            (shift b))) := by
  unfold GorbowStandardInduction.successorInstance condFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftSucc] <;> rfl

theorem internalConditional : GorbowPRInternalControl.Targets.InternalConditional := by
  intro n p tag h ctx x a b
  obtain ⟨c0⟩ := conditionalZero p tag h ctx a b
  obtain ⟨cS⟩ := conditionalSucc p tag h (ctx + 1) (.var 0) (shift a) (shift b)
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (condFormula tag a b) .zero) := by
    rw [condInst]
    exact conjI (liftK _ c0) (posNegImp (.logical (.reflexive .zero)) _)
  have stepBody : Derivation (Theory p) (.conj
      (.imp (.equal (Term.succ (Term.var 0)) .zero)
        (.equal (call tag (Term.succ (Term.var 0) ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil))
          (shift a)))
      (.imp (.neg (.equal (Term.succ (Term.var 0)) .zero))
        (.equal (call tag (Term.succ (Term.var 0) ::ᵥ shift a ::ᵥ shift b ::ᵥ List.Vector.nil))
          (shift b)))) :=
    conjI (negImp (.arithmetic (.succNotZero (.var 0))) _) (liftK _ cS)
  have step : Derivation (Theory p) (.imp (condFormula tag a b)
      (GorbowStandardInduction.successorInstance (condFormula tag a b))) := by
    rw [condSuccInst]
    exact liftK _ stepBody
  obtain ⟨d⟩ := objectInduction (condFormula tag a b) base step x
  rw [condInst] at d
  exact ⟨d⟩

theorem fullTarget : GorbowPRInternalControl.Targets.Target :=
  ⟨actualEvaluation, internalZeroTest, internalBooleanRange, internalConditional⟩

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.Proof
