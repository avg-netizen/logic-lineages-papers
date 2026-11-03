module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
/-! Internal arithmetic for the fixed literal addition, multiplication and
pairing ASTs. External evaluation is proved by recursion on the counter.
Internally, the symbolic node equations at actual child tags give the defining
recursion equations; addition and multiplication are then proved by the
calculus's own induction instance, with the induction hypothesis kept as an
object implication. Pairing composes these at its actual child tags in the
fixed input order, ending at the literal `pairTerm`. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.Proof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry GorbowSubstitution
open GorbowPRDefiningEquations (call argumentVariables nodeEquations)
open GorbowPRNumeralCalculation (Theory)
open List.Vector

/-! ### Named argument families of the fixed ASTs -/

private def mulStepArg (i : Fin 2) : Program 3 :=
  if i.val = 0 then .projection (2 : Fin 3) else .projection (1 : Fin 3)

private def sumArg (i : Fin 2) : Program 2 :=
  if i.val = 0 then .projection (1 : Fin 2) else .projection (0 : Fin 2)

private def pairArg : Fin 2 → Program 2 :=
  Fin.cases (.projection (0 : Fin 2)) (fun _ : Fin 1 => squareSum)

/-! ### External evaluation -/

private theorem stepAddEval (k prev x : Nat) :
    evaluate additionStep (k ::ᵥ prev ::ᵥ x ::ᵥ List.Vector.nil) = Nat.succ prev := by
  first
    | rfl
    | (show Nat.succ (List.Vector.ofFn (fun _ : Fin 1 =>
          evaluate (.projection (1 : Fin 3)) (k ::ᵥ prev ::ᵥ x ::ᵥ List.Vector.nil))).head =
          Nat.succ prev
       rw [← List.Vector.get_zero, List.Vector.get_ofFn]
       rfl)
    | simp [additionStep, evaluate]

private theorem evalAdd (x : Nat) : ∀ y : Nat,
    evaluate addition (y ::ᵥ x ::ᵥ List.Vector.nil) = x + y
  | 0 => GorbowPRProgram.Proof.recursionZero 1 additionBase additionStep (x ::ᵥ List.Vector.nil)
  | y + 1 =>
    (GorbowPRProgram.Proof.recursionSuccessor 1 additionBase additionStep
      (x ::ᵥ List.Vector.nil) y).trans
      ((stepAddEval y (evaluate addition (y ::ᵥ x ::ᵥ List.Vector.nil)) x).trans
        (congrArg Nat.succ (evalAdd x y)))

private theorem stepMulEval (k prev x : Nat) :
    evaluate multiplicationStep (k ::ᵥ prev ::ᵥ x ::ᵥ List.Vector.nil) = prev + x := by
  have hv : (List.Vector.ofFn fun i : Fin 2 =>
      evaluate (mulStepArg i) (k ::ᵥ prev ::ᵥ x ::ᵥ List.Vector.nil)) =
      x ::ᵥ prev ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl : j = 0 := Fin.eq_zero j
      rfl
  show evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (mulStepArg i) (k ::ᵥ prev ::ᵥ x ::ᵥ List.Vector.nil)) = prev + x
  rw [hv]
  exact evalAdd prev x

private theorem evalMul (x : Nat) : ∀ y : Nat,
    evaluate multiplication (y ::ᵥ x ::ᵥ List.Vector.nil) = x * y
  | 0 => GorbowPRProgram.Proof.recursionZero 1 multiplicationBase multiplicationStep
      (x ::ᵥ List.Vector.nil)
  | y + 1 =>
    (GorbowPRProgram.Proof.recursionSuccessor 1 multiplicationBase multiplicationStep
      (x ::ᵥ List.Vector.nil) y).trans
      ((stepMulEval y (evaluate multiplication (y ::ᵥ x ::ᵥ List.Vector.nil)) x).trans
        (congrArg (· + x) (evalMul x y)))

private theorem evalSum (a b : Nat) :
    evaluate sumInputs (a ::ᵥ b ::ᵥ List.Vector.nil) = a + b := by
  have hv : (List.Vector.ofFn fun i : Fin 2 =>
      evaluate (sumArg i) (a ::ᵥ b ::ᵥ List.Vector.nil)) = b ::ᵥ a ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl : j = 0 := Fin.eq_zero j
      rfl
  show evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (sumArg i) (a ::ᵥ b ::ᵥ List.Vector.nil)) = a + b
  rw [hv]
  exact evalAdd a b

private theorem evalSquare (a b : Nat) :
    evaluate squareSum (a ::ᵥ b ::ᵥ List.Vector.nil) = (a + b) * (a + b) := by
  have hv : (List.Vector.ofFn fun _ : Fin 2 =>
      evaluate sumInputs (a ::ᵥ b ::ᵥ List.Vector.nil)) =
      (a + b) ::ᵥ (a + b) ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn, evalSum]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl : j = 0 := Fin.eq_zero j
      rfl
  show evaluate multiplication (List.Vector.ofFn fun _ : Fin 2 =>
    evaluate sumInputs (a ::ᵥ b ::ᵥ List.Vector.nil)) = (a + b) * (a + b)
  rw [hv]
  exact evalMul (a + b) (a + b)

private theorem evalPair (a b : Nat) :
    evaluate pairing (a ::ᵥ b ::ᵥ List.Vector.nil) = GorbowRegistryTuple.pair a b := by
  have hv : (List.Vector.ofFn fun i : Fin 2 =>
      evaluate (pairArg i) (a ::ᵥ b ::ᵥ List.Vector.nil)) =
      a ::ᵥ (a + b) * (a + b) ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl : j = 0 := Fin.eq_zero j
      exact evalSquare a b
  show evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (pairArg i) (a ::ᵥ b ::ᵥ List.Vector.nil)) = GorbowRegistryTuple.pair a b
  rw [hv]
  exact evalAdd ((a + b) * (a + b)) a

theorem actualEvaluation : GorbowPRInternalArithmetic.Targets.ActualEvaluation :=
  ⟨fun x y => evalAdd x y, fun x y => evalMul x y, fun a b => evalPair a b⟩

/-! ### Propositional combinators and equality reasoning -/

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

private def implicationIdentity (A : Sentence → Prop) {n : Nat} (a : Formula n) :
    Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

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

private theorem condRewrite {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx)
    (L : Term ctx) (M : Term (ctx + 1)) (a b Ma Mb : Term ctx)
    (ha : substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) M = Ma)
    (hb : substitute (Fin.cases b Term.var : Fin (ctx + 1) → Term ctx) M = Mb)
    (hab : Derivation A (.imp R (.equal a b))) (h : Derivation A (.imp R (.equal L Ma))) :
    Nonempty (Derivation A (.imp R (.equal L Mb))) := by
  have e : Derivation A (.imp (.equal a b)
      (.imp (GorbowStandardInstances.instantiate (.equal (shift L) M) a)
        (GorbowStandardInstances.instantiate (.equal (shift L) M) b))) :=
    .logical (.equalityReplace (.equal (shift L) M) a b)
  rw [instShiftEqual, instShiftEqual, ha, hb] at e
  exact ⟨mpUnder (compose e hab) h⟩

private theorem condTrans {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b c : Term ctx}
    (h1 : Derivation A (.imp R (.equal a b))) (h2 : Derivation A (.imp R (.equal b c))) :
    Nonempty (Derivation A (.imp R (.equal a c))) :=
  condRewrite R a (.var 0) b c b c rfl rfl h2 h1

private theorem condSymm {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b : Term ctx}
    (h : Derivation A (.imp R (.equal a b))) :
    Nonempty (Derivation A (.imp R (.equal b a))) := by
  have e : Derivation A (.imp (.equal a b)
      (.imp (GorbowStandardInstances.instantiate (.equal (.var 0) (shift a)) a)
        (GorbowStandardInstances.instantiate (.equal (.var 0) (shift a)) b))) :=
    .logical (.equalityReplace (.equal (.var 0) (shift a)) a b)
  rw [instShiftEqualR, instShiftEqualR] at e
  exact ⟨mpUnder (compose e h) (liftK R (.logical (.reflexive a)))⟩

private theorem eqTrans {A : Sentence → Prop} {ctx : Nat} {a b c : Term ctx}
    (h1 : Derivation A (.equal a b)) (h2 : Derivation A (.equal b c)) :
    Nonempty (Derivation A (.equal a c)) := by
  obtain ⟨d⟩ := condTrans (.equal .zero .zero) (liftK (.equal .zero .zero) h1)
    (liftK (.equal .zero .zero) h2)
  exact ⟨.mp d (.logical (.reflexive .zero))⟩

private theorem eqSymm {A : Sentence → Prop} {ctx : Nat} {a b : Term ctx}
    (h : Derivation A (.equal a b)) : Nonempty (Derivation A (.equal b a)) := by
  obtain ⟨d⟩ := condSymm (.equal .zero .zero) (liftK (.equal .zero .zero) h)
  exact ⟨.mp d (.logical (.reflexive .zero))⟩

private theorem condSucc {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) :
    Nonempty (Derivation A (.imp R (.equal (.succ a) (.succ b)))) :=
  condRewrite R (.succ a) (.succ (.var 0)) a b (.succ a) (.succ b) rfl rfl hab
    (liftK R (.logical (.reflexive (.succ a))))

private theorem condAdd {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b c d : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) (hcd : Derivation A (.imp R (.equal c d))) :
    Nonempty (Derivation A (.imp R (.equal (.add a c) (.add b d)))) := by
  obtain ⟨h1⟩ := condRewrite R (.add a c) (.add (.var 0) (shift c)) a b (.add a c) (.add b c)
    (congrArg (Term.add a) (shiftInst a c)) (congrArg (Term.add b) (shiftInst b c)) hab
    (liftK R (.logical (.reflexive (.add a c))))
  exact condRewrite R (.add a c) (.add (shift b) (.var 0)) c d (.add b c) (.add b d)
    (congrArg (fun x => Term.add x c) (shiftInst c b))
    (congrArg (fun x => Term.add x d) (shiftInst d b)) hcd h1

/-! ### Call congruence and node values -/

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

/-! ### Actual child lookups -/

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

/-- A composition node equals its function child applied to known child values. -/
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

/-! ### Step and base node values -/

private theorem addStepValue {n : Nat} (p : Program n) (tagS : Nat)
    (h : (nodes p)[tagS]? = some ⟨3, additionStep⟩) (ctx : Nat) (k P X : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tagS (k ::ᵥ P ::ᵥ X ::ᵥ List.Vector.nil)) (.succ P))) := by
  have hf := compFunLookup p tagS .succ (fun _ : Fin 1 => .projection (1 : Fin 3)) h
  obtain ⟨c⟩ := compValue p tagS .succ (fun _ : Fin 1 => .projection (1 : Fin 3)) h ctx
    (k ::ᵥ P ::ᵥ X ::ᵥ List.Vector.nil) (P ::ᵥ List.Vector.nil)
    (fun i => by
      obtain rfl : i = 0 := Fin.eq_zero i
      exact projectionValueAt p _ (1 : Fin 3)
        (compArgLookup p tagS .succ (fun _ : Fin 1 => .projection (1 : Fin 3)) h 0) ctx _ _
        (by first | rfl | simp))
  obtain ⟨sv⟩ := succValue p (tagS + 1) hf ctx (P ::ᵥ List.Vector.nil)
  exact eqTrans c sv

private theorem mulBaseValue {n : Nat} (p : Program n) (tagB : Nat)
    (h : (nodes p)[tagB]? = some ⟨1, multiplicationBase⟩) (ctx : Nat) (x : Term ctx) :
    Nonempty (Derivation (Theory p) (.equal (call tagB (x ::ᵥ List.Vector.nil)) .zero)) := by
  have hf := compFunLookup p tagB .zero (Fin.elim0 : Fin 0 → Program 1) h
  obtain ⟨c⟩ := compValue p tagB .zero (Fin.elim0 : Fin 0 → Program 1) h ctx
    (x ::ᵥ List.Vector.nil) List.Vector.nil (fun i => Fin.elim0 i)
  obtain ⟨zv⟩ := zeroValue p (tagB + 1) hf ctx List.Vector.nil
  exact eqTrans c zv

/-! ### Internal addition by object induction -/

private def addFormula {ctx : Nat} (tag : Nat) (x : Term ctx) : Formula (ctx + 1) :=
  .equal (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil)) (.add (shift x) (Term.var 0))

private theorem subAddInst {ctx : Nat} (x t : Term ctx) :
    substitute (Fin.cases t Term.var : Fin (ctx + 1) → Term ctx)
      (Term.add (shift x) (Term.var 0)) = Term.add x t :=
  congrArg (fun z => Term.add z t) (shiftInst t x)

private theorem subAddSucc {ctx : Nat} (x : Term ctx) :
    substitute (Fin.cases (Term.succ (Term.var 0)) (fun i : Fin ctx => Term.var i.succ) :
      Fin (ctx + 1) → Term (ctx + 1)) (Term.add (shift x) (Term.var 0)) =
      Term.add (shift x) (Term.succ (Term.var 0)) :=
  congrArg (fun z => Term.add z (Term.succ (Term.var 0))) (shiftSucc x)

private theorem addInst {ctx : Nat} (tag : Nat) (x t : Term ctx) :
    GorbowStandardInstances.instantiate (addFormula tag x) t =
      .equal (call tag (t ::ᵥ x ::ᵥ List.Vector.nil)) (.add x t) := by
  unfold GorbowStandardInstances.instantiate addFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftInst, subAddInst] <;> rfl

private theorem addSuccInst {ctx : Nat} (tag : Nat) (x : Term ctx) :
    GorbowStandardInduction.successorInstance (addFormula tag x) =
      .equal (call tag (Term.succ (Term.var 0) ::ᵥ shift x ::ᵥ List.Vector.nil))
        (.add (shift x) (Term.succ (Term.var 0))) := by
  unfold GorbowStandardInduction.successorInstance addFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftSucc, subAddSucc] <;> rfl

private theorem addCore {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨2, addition⟩) (ctx : Nat) (x y : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (y ::ᵥ x ::ᵥ List.Vector.nil)) (.add x y))) := by
  have hb := recBaseLookup p tag additionBase additionStep h
  have hs := recStepLookup p tag additionBase additionStep h
  -- Base: call(0,x) = x = x + 0.
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1
    additionBase additionStep h ctx (x ::ᵥ List.Vector.nil)
  obtain ⟨z2⟩ := projectionValue p (tag + 1) (0 : Fin 1) hb ctx (x ::ᵥ List.Vector.nil)
  have z3 : Derivation (Theory p) (.equal (.add x .zero) x) := .arithmetic (.addZero x)
  obtain ⟨z3'⟩ := eqSymm z3
  obtain ⟨b1⟩ := eqTrans z1 z2
  obtain ⟨b2⟩ := eqTrans b1 z3'
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (addFormula tag x) .zero) := by
    rw [addInst]
    exact b2
  -- Step: phi -> successorInstance phi, as an object implication.
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1
    additionBase additionStep h (ctx + 1) (.var 0) (shift x ::ᵥ List.Vector.nil)
  obtain ⟨s2⟩ := addStepValue p (tag + GorbowPRChildTags.stepTag additionBase) hs (ctx + 1)
    (.var 0) (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil)) (shift x)
  have hP : Derivation (Theory p) (.imp (addFormula tag x)
      (.equal (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil))
        (.add (shift x) (Term.var 0)))) :=
    implicationIdentity _ _
  obtain ⟨c⟩ := condSucc (addFormula tag x) hP
  have s4 : Derivation (Theory p) (.equal (.add (shift x) (.succ (Term.var 0)))
      (.succ (.add (shift x) (Term.var 0)))) := .arithmetic (.addSucc (shift x) (.var 0))
  obtain ⟨s4'⟩ := eqSymm s4
  obtain ⟨u1⟩ := condTrans (addFormula tag x) (liftK (addFormula tag x) s1)
    (liftK (addFormula tag x) s2)
  obtain ⟨u2⟩ := condTrans (addFormula tag x) u1 c
  obtain ⟨u3⟩ := condTrans (addFormula tag x) u2 (liftK (addFormula tag x) s4')
  have step : Derivation (Theory p) (.imp (addFormula tag x)
      (GorbowStandardInduction.successorInstance (addFormula tag x))) := by
    rw [addSuccInst]
    exact u3
  -- The actual induction instance, generalization and instantiation at y.
  have ind : Derivation (Theory p) (GorbowStandardInduction.inductionAxiom (addFormula tag x)) :=
    .arithmetic (.induction (addFormula tag x))
  have hall : Derivation (Theory p) (.all (addFormula tag x)) :=
    .mp (.mp ind base) (.generalize step)
  have hfin : Derivation (Theory p) (GorbowStandardInstances.instantiate (addFormula tag x) y) :=
    .mp (.logical (.allInstantiate (addFormula tag x) y)) hall
  rw [addInst] at hfin
  exact ⟨hfin⟩

theorem internalAddition : GorbowPRInternalArithmetic.Targets.InternalAddition := by
  intro n p tag h ctx x y
  exact addCore p tag h ctx x y

/-! ### Internal multiplication by object induction -/

private theorem mulStepValue {n : Nat} (p : Program n) (tagS : Nat)
    (h : (nodes p)[tagS]? = some ⟨3, multiplicationStep⟩) (ctx : Nat) (k P X : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tagS (k ::ᵥ P ::ᵥ X ::ᵥ List.Vector.nil)) (.add P X))) := by
  have hf := compFunLookup p tagS addition mulStepArg h
  obtain ⟨c⟩ := compValue p tagS addition mulStepArg h ctx
    (k ::ᵥ P ::ᵥ X ::ᵥ List.Vector.nil) (X ::ᵥ P ::ᵥ List.Vector.nil)
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact projectionValueAt p _ (2 : Fin 3) (compArgLookup p tagS addition mulStepArg h 0)
          ctx _ _ (by first | rfl | simp)
      · obtain rfl : j = 0 := Fin.eq_zero j
        exact projectionValueAt p _ (1 : Fin 3)
          (compArgLookup p tagS addition mulStepArg h (Fin.succ 0)) ctx _ _
          (by first | rfl | simp))
  obtain ⟨av⟩ := addCore p (tagS + 1) hf ctx P X
  exact eqTrans c av

private def mulFormula {ctx : Nat} (tag : Nat) (x : Term ctx) : Formula (ctx + 1) :=
  .equal (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil)) (.mul (shift x) (Term.var 0))

private theorem subMulInst {ctx : Nat} (x t : Term ctx) :
    substitute (Fin.cases t Term.var : Fin (ctx + 1) → Term ctx)
      (Term.mul (shift x) (Term.var 0)) = Term.mul x t :=
  congrArg (fun z => Term.mul z t) (shiftInst t x)

private theorem subMulSucc {ctx : Nat} (x : Term ctx) :
    substitute (Fin.cases (Term.succ (Term.var 0)) (fun i : Fin ctx => Term.var i.succ) :
      Fin (ctx + 1) → Term (ctx + 1)) (Term.mul (shift x) (Term.var 0)) =
      Term.mul (shift x) (Term.succ (Term.var 0)) :=
  congrArg (fun z => Term.mul z (Term.succ (Term.var 0))) (shiftSucc x)

private theorem mulInst {ctx : Nat} (tag : Nat) (x t : Term ctx) :
    GorbowStandardInstances.instantiate (mulFormula tag x) t =
      .equal (call tag (t ::ᵥ x ::ᵥ List.Vector.nil)) (.mul x t) := by
  unfold GorbowStandardInstances.instantiate mulFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftInst, subMulInst] <;> rfl

private theorem mulSuccInst {ctx : Nat} (tag : Nat) (x : Term ctx) :
    GorbowStandardInduction.successorInstance (mulFormula tag x) =
      .equal (call tag (Term.succ (Term.var 0) ::ᵥ shift x ::ᵥ List.Vector.nil))
        (.mul (shift x) (Term.succ (Term.var 0))) := by
  unfold GorbowStandardInduction.successorInstance mulFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    List.Vector.map_nil, shiftSucc, subMulSucc] <;> rfl

private theorem mulCore {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨2, multiplication⟩) (ctx : Nat) (x y : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (y ::ᵥ x ::ᵥ List.Vector.nil)) (.mul x y))) := by
  have hb := recBaseLookup p tag multiplicationBase multiplicationStep h
  have hs := recStepLookup p tag multiplicationBase multiplicationStep h
  -- Base: call(0,x) = 0 = x * 0.
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1
    multiplicationBase multiplicationStep h ctx (x ::ᵥ List.Vector.nil)
  obtain ⟨z2⟩ := mulBaseValue p (tag + 1) hb ctx x
  have z3 : Derivation (Theory p) (.equal (.mul x .zero) .zero) := .arithmetic (.mulZero x)
  obtain ⟨z3'⟩ := eqSymm z3
  obtain ⟨b1⟩ := eqTrans z1 z2
  obtain ⟨b2⟩ := eqTrans b1 z3'
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (mulFormula tag x) .zero) := by
    rw [mulInst]
    exact b2
  -- Step: the step child contains the actual addition AST at its function tag.
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1
    multiplicationBase multiplicationStep h (ctx + 1) (.var 0) (shift x ::ᵥ List.Vector.nil)
  obtain ⟨s2⟩ := mulStepValue p (tag + GorbowPRChildTags.stepTag multiplicationBase) hs (ctx + 1)
    (.var 0) (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil)) (shift x)
  have hP : Derivation (Theory p) (.imp (mulFormula tag x)
      (.equal (call tag (Term.var 0 ::ᵥ shift x ::ᵥ List.Vector.nil))
        (.mul (shift x) (Term.var 0)))) :=
    implicationIdentity _ _
  obtain ⟨c⟩ := condAdd (mulFormula tag x) hP
    (liftK (mulFormula tag x) (.logical (.reflexive (shift x))))
  have s4 : Derivation (Theory p) (.equal (.mul (shift x) (.succ (Term.var 0)))
      (.add (.mul (shift x) (Term.var 0)) (shift x))) := .arithmetic (.mulSucc (shift x) (.var 0))
  obtain ⟨s4'⟩ := eqSymm s4
  obtain ⟨u1⟩ := condTrans (mulFormula tag x) (liftK (mulFormula tag x) s1)
    (liftK (mulFormula tag x) s2)
  obtain ⟨u2⟩ := condTrans (mulFormula tag x) u1 c
  obtain ⟨u3⟩ := condTrans (mulFormula tag x) u2 (liftK (mulFormula tag x) s4')
  have step : Derivation (Theory p) (.imp (mulFormula tag x)
      (GorbowStandardInduction.successorInstance (mulFormula tag x))) := by
    rw [mulSuccInst]
    exact u3
  have ind : Derivation (Theory p) (GorbowStandardInduction.inductionAxiom (mulFormula tag x)) :=
    .arithmetic (.induction (mulFormula tag x))
  have hall : Derivation (Theory p) (.all (mulFormula tag x)) :=
    .mp (.mp ind base) (.generalize step)
  have hfin : Derivation (Theory p) (GorbowStandardInstances.instantiate (mulFormula tag x) y) :=
    .mp (.logical (.allInstantiate (mulFormula tag x) y)) hall
  rw [mulInst] at hfin
  exact ⟨hfin⟩

theorem internalMultiplication : GorbowPRInternalArithmetic.Targets.InternalMultiplication := by
  intro n p tag h ctx x y
  exact mulCore p tag h ctx x y

/-! ### Internal pairing at the actual child tags -/

private theorem sumValue {n : Nat} (p : Program n) (tagU : Nat)
    (h : (nodes p)[tagU]? = some ⟨2, sumInputs⟩) (ctx : Nat) (a b : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tagU (a ::ᵥ b ::ᵥ List.Vector.nil)) (.add a b))) := by
  have hf := compFunLookup p tagU addition sumArg h
  obtain ⟨c⟩ := compValue p tagU addition sumArg h ctx (a ::ᵥ b ::ᵥ List.Vector.nil)
    (b ::ᵥ a ::ᵥ List.Vector.nil)
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact projectionValueAt p _ (1 : Fin 2) (compArgLookup p tagU addition sumArg h 0)
          ctx _ _ (by first | rfl | simp)
      · obtain rfl : j = 0 := Fin.eq_zero j
        exact projectionValueAt p _ (0 : Fin 2)
          (compArgLookup p tagU addition sumArg h (Fin.succ 0)) ctx _ _
          (by first | rfl | simp))
  obtain ⟨av⟩ := addCore p (tagU + 1) hf ctx a b
  exact eqTrans c av

private theorem squareValue {n : Nat} (p : Program n) (tagQ : Nat)
    (h : (nodes p)[tagQ]? = some ⟨2, squareSum⟩) (ctx : Nat) (a b : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tagQ (a ::ᵥ b ::ᵥ List.Vector.nil)) (.mul (.add a b) (.add a b)))) := by
  have hf := compFunLookup p tagQ multiplication (fun _ : Fin 2 => sumInputs) h
  obtain ⟨c⟩ := compValue p tagQ multiplication (fun _ : Fin 2 => sumInputs) h ctx
    (a ::ᵥ b ::ᵥ List.Vector.nil) (Term.add a b ::ᵥ Term.add a b ::ᵥ List.Vector.nil)
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sumValue p _
          (compArgLookup p tagQ multiplication (fun _ : Fin 2 => sumInputs) h 0) ctx a b
      · obtain rfl : j = 0 := Fin.eq_zero j
        exact sumValue p _
          (compArgLookup p tagQ multiplication (fun _ : Fin 2 => sumInputs) h (Fin.succ 0))
          ctx a b)
  obtain ⟨mv⟩ := mulCore p (tagQ + 1) hf ctx (.add a b) (.add a b)
  exact eqTrans c mv

private theorem pairCore {n : Nat} (p : Program n) (tag : Nat)
    (h : (nodes p)[tag]? = some ⟨2, pairing⟩) (ctx : Nat) (a b : Term ctx) :
    Nonempty (Derivation (Theory p)
      (.equal (call tag (a ::ᵥ b ::ᵥ List.Vector.nil)) (GorbowRegistryTuple.pairTerm a b))) := by
  have hf := compFunLookup p tag addition pairArg h
  obtain ⟨c⟩ := compValue p tag addition pairArg h ctx (a ::ᵥ b ::ᵥ List.Vector.nil)
    (a ::ᵥ Term.mul (Term.add a b) (Term.add a b) ::ᵥ List.Vector.nil)
    (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact projectionValueAt p _ (0 : Fin 2) (compArgLookup p tag addition pairArg h 0)
          ctx _ _ (by first | rfl | simp)
      · obtain rfl : j = 0 := Fin.eq_zero j
        exact squareValue p _ (compArgLookup p tag addition pairArg h (Fin.succ 0)) ctx a b)
  obtain ⟨av⟩ := addCore p (tag + 1) hf ctx (Term.mul (Term.add a b) (Term.add a b)) a
  exact eqTrans c av

theorem internalPairing : GorbowPRInternalArithmetic.Targets.InternalPairing := by
  intro n p tag h ctx a b
  exact pairCore p tag h ctx a b

theorem fullTarget : GorbowPRInternalArithmetic.Targets.Target :=
  ⟨actualEvaluation, internalAddition, internalMultiplication, internalPairing⟩

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.Proof
