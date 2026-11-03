module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! Internal coherence of duplicate occurrences of one PR AST. Open and
conditional congruence are derived from `equalityReplace`, `reflexive` and the
S/K rules, with retained terms shifted into the fresh context. Registry
coherence is structural induction on the common program; the recursive case
uses the calculus's own induction instance with the induction hypothesis kept
as an object implication, then generalization and instantiation at the
original head argument. No open formula is installed as an axiom, and no
external evaluation is turned into a proof. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.Proof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry GorbowSubstitution
open GorbowPRDefiningEquations (call argumentVariables nodeEquations)
open GorbowPRNumeralCalculation (Theory)
open List.Vector

/-! ### Propositional combinators -/

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

/-! ### Shifting retained terms into the fresh context -/

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

/-! ### Conditional equality reasoning under an open antecedent -/

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

/-! ### Constructor congruences under an open antecedent -/

private theorem condSucc {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) :
    Nonempty (Derivation A (.imp R (.equal (.succ a) (.succ b)))) :=
  condRewrite R (.succ a) (.succ (.var 0)) a b (.succ a) (.succ b) rfl rfl hab
    (liftK R (.logical (.reflexive (.succ a))))

private theorem condFunction {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) :
    Nonempty (Derivation A (.imp R (.equal (.universalFunction a) (.universalFunction b)))) :=
  condRewrite R (.universalFunction a) (.universalFunction (.var 0)) a b
    (.universalFunction a) (.universalFunction b) rfl rfl hab
    (liftK R (.logical (.reflexive (.universalFunction a))))

private theorem condAdd {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b c d : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) (hcd : Derivation A (.imp R (.equal c d))) :
    Nonempty (Derivation A (.imp R (.equal (.add a c) (.add b d)))) := by
  obtain ⟨h1⟩ := condRewrite R (.add a c) (.add (.var 0) (shift c)) a b (.add a c) (.add b c)
    (congrArg (Term.add a) (shiftInst a c)) (congrArg (Term.add b) (shiftInst b c)) hab
    (liftK R (.logical (.reflexive (.add a c))))
  exact condRewrite R (.add a c) (.add (shift b) (.var 0)) c d (.add b c) (.add b d)
    (congrArg (fun x => Term.add x c) (shiftInst c b))
    (congrArg (fun x => Term.add x d) (shiftInst d b)) hcd h1

private theorem condMul {A : Sentence → Prop} {ctx : Nat} (R : Formula ctx) {a b c d : Term ctx}
    (hab : Derivation A (.imp R (.equal a b))) (hcd : Derivation A (.imp R (.equal c d))) :
    Nonempty (Derivation A (.imp R (.equal (.mul a c) (.mul b d)))) := by
  obtain ⟨h1⟩ := condRewrite R (.mul a c) (.mul (.var 0) (shift c)) a b (.mul a c) (.mul b c)
    (congrArg (Term.mul a) (shiftInst a c)) (congrArg (Term.mul b) (shiftInst b c)) hab
    (liftK R (.logical (.reflexive (.mul a c))))
  exact condRewrite R (.mul a c) (.mul (shift b) (.var 0)) c d (.mul b c) (.mul b d)
    (congrArg (fun x => Term.mul x c) (shiftInst c b))
    (congrArg (fun x => Term.mul x d) (shiftInst d b)) hcd h1

private theorem condCongruence {A : Sentence → Prop} {n ctx : Nat} (R : Formula ctx)
    (σ τ : Fin n → Term ctx) (h : ∀ i, Nonempty (Derivation A (.imp R (.equal (σ i) (τ i)))))
    (t : Term n) :
    Nonempty (Derivation A (.imp R (.equal (substitute σ t) (substitute τ t)))) := by
  induction t with
  | var i => exact h i
  | zero => exact ⟨liftK R (.logical (.reflexive .zero))⟩
  | succ t ih =>
    obtain ⟨p⟩ := ih
    exact condSucc R p
  | add t u iht ihu =>
    obtain ⟨p⟩ := iht
    obtain ⟨q⟩ := ihu
    exact condAdd R p q
  | mul t u iht ihu =>
    obtain ⟨p⟩ := iht
    obtain ⟨q⟩ := ihu
    exact condMul R p q
  | universalFunction t ih =>
    obtain ⟨p⟩ := ih
    exact condFunction R p

theorem conditionalTermCongruence :
    GorbowPRInternalCoherence.Targets.ConditionalTermCongruence := by
  intro A n ctx R t σ τ h
  exact condCongruence R σ τ h t

theorem openTermCongruence : GorbowPRInternalCoherence.Targets.OpenTermCongruence := by
  intro A n ctx t σ τ h
  obtain ⟨d⟩ := condCongruence (A := A) (.equal .zero .zero) σ τ
    (fun i => (h i).elim fun p => ⟨liftK _ p⟩) t
  exact ⟨.mp d (.logical (.reflexive .zero))⟩

/-! ### Call congruence in arbitrary contexts -/

private theorem sub_call {arity ctx out : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem sub_arguments {arity ctx : Nat} (args : List.Vector (Term ctx) arity) :
    (argumentVariables arity).map (substitute args.get) = args := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables, substitute]

private theorem condCallCong {A : Sentence → Prop} {ctx k : Nat} (R : Formula ctx) (tag : Nat)
    (v w : List.Vector (Term ctx) k)
    (h : ∀ i, Nonempty (Derivation A (.imp R (.equal (v.get i) (w.get i))))) :
    Nonempty (Derivation A (.imp R (.equal (call tag v) (call tag w)))) := by
  obtain ⟨d⟩ := condCongruence R v.get w.get h (call tag (argumentVariables k))
  rw [sub_call, sub_call, sub_arguments, sub_arguments] at d
  exact ⟨d⟩

private theorem callCong {A : Sentence → Prop} {ctx k : Nat} (tag : Nat)
    (v w : List.Vector (Term ctx) k)
    (h : ∀ i, Nonempty (Derivation A (.equal (v.get i) (w.get i)))) :
    Nonempty (Derivation A (.equal (call tag v) (call tag w))) := by
  obtain ⟨d⟩ := condCallCong (A := A) (.equal .zero .zero) tag v w
    (fun i => (h i).elim fun p => ⟨liftK _ p⟩)
  exact ⟨.mp d (.logical (.reflexive .zero))⟩

/-! ### Primitive node values -/

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

/-! ### The object induction formula for a recursive node -/

/-- Variable0 is the induction variable; the tail arguments are shifted. -/
private def recFormula {k ctx : Nat} (tagL tagR : Nat) (tail : List.Vector (Term ctx) k) :
    Formula (ctx + 1) :=
  .equal (call tagL (Term.var 0 ::ᵥ tail.map shift)) (call tagR (Term.var 0 ::ᵥ tail.map shift))

private theorem mapShiftInst {k ctx : Nat} (a : Term ctx) (tail : List.Vector (Term ctx) k) :
    (tail.map shift).map (substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx)) = tail := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map, shiftInst]

private theorem mapShiftSucc {k ctx : Nat} (tail : List.Vector (Term ctx) k) :
    (tail.map shift).map (substitute (Fin.cases (Term.succ (Term.var 0))
      (fun i : Fin ctx => Term.var i.succ) : Fin (ctx + 1) → Term (ctx + 1))) =
      tail.map shift := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map, shiftSucc]

private theorem phiInst {k ctx : Nat} (tagL tagR : Nat) (tail : List.Vector (Term ctx) k)
    (t : Term ctx) :
    GorbowStandardInstances.instantiate (recFormula tagL tagR tail) t =
      .equal (call tagL (t ::ᵥ tail)) (call tagR (t ::ᵥ tail)) := by
  unfold GorbowStandardInstances.instantiate recFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    mapShiftInst] <;> rfl

private theorem phiSucc {k ctx : Nat} (tagL tagR : Nat) (tail : List.Vector (Term ctx) k) :
    GorbowStandardInduction.successorInstance (recFormula tagL tagR tail) =
      .equal (call tagL (Term.succ (Term.var 0) ::ᵥ tail.map shift))
        (call tagR (Term.succ (Term.var 0) ::ᵥ tail.map shift)) := by
  unfold GorbowStandardInduction.successorInstance recFormula
  simp only [GorbowFormulaSubstitution.substituteFormula, sub_call, List.Vector.map_cons,
    mapShiftSucc] <;> rfl

private theorem recursionCoherence {n k : Nat} (p : Program n) (f : Program k)
    (g : Program (k + 2)) (tagL tagR : Nat)
    (hL : (nodes p)[tagL]? = some ⟨k + 1, .recursion f g⟩)
    (hR : (nodes p)[tagR]? = some ⟨k + 1, .recursion f g⟩)
    (IHf : ∀ ctx (v : List.Vector (Term ctx) k),
      Nonempty (Derivation (Theory p) (.equal (call (tagL + 1) v) (call (tagR + 1) v))))
    (IHg : ∀ ctx (v : List.Vector (Term ctx) (k + 2)),
      Nonempty (Derivation (Theory p) (.equal (call (tagL + GorbowPRChildTags.stepTag f) v)
        (call (tagR + GorbowPRChildTags.stepTag f) v))))
    (ctx : Nat) (args : List.Vector (Term ctx) (k + 1)) :
    Nonempty (Derivation (Theory p) (.equal (call tagL args) (call tagR args))) := by
  obtain ⟨x, tail, rfl⟩ : ∃ (x : Term ctx) (tail : List.Vector (Term ctx) k),
      args = x ::ᵥ tail := ⟨args.head, args.tail, (List.Vector.cons_head_tail args).symm⟩
  -- Base: recursion-zero equations and the base-program coherence.
  obtain ⟨z1⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tagL k f g hL ctx tail
  obtain ⟨z2⟩ := IHf ctx tail
  obtain ⟨z3⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tagR k f g hR ctx tail
  obtain ⟨z3'⟩ := eqSymm z3
  obtain ⟨b1⟩ := eqTrans z1 z2
  obtain ⟨b2⟩ := eqTrans b1 z3'
  have base : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (recFormula tagL tagR tail) .zero) := by
    rw [phiInst]
    exact b2
  -- Step: an actual derivation of phi -> successorInstance phi in context ctx+1.
  obtain ⟨s1⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tagL k f g hL
    (ctx + 1) (.var 0) (tail.map shift)
  obtain ⟨s3⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tagR k f g hR
    (ctx + 1) (.var 0) (tail.map shift)
  obtain ⟨s3'⟩ := eqSymm s3
  obtain ⟨s2⟩ := IHg (ctx + 1)
    (Term.var 0 ::ᵥ call tagR (Term.var 0 ::ᵥ tail.map shift) ::ᵥ tail.map shift)
  obtain ⟨cg⟩ := condCallCong (A := Theory p) (recFormula tagL tagR tail)
    (tagL + GorbowPRChildTags.stepTag f)
    (Term.var 0 ::ᵥ call tagL (Term.var 0 ::ᵥ tail.map shift) ::ᵥ tail.map shift)
    (Term.var 0 ::ᵥ call tagR (Term.var 0 ::ᵥ tail.map shift) ::ᵥ tail.map shift)
    (by
      intro i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
      · simp only [List.Vector.get_cons_zero]
        exact ⟨liftK _ (.logical (.reflexive _))⟩
      · simp only [List.Vector.get_cons_succ, List.Vector.get_cons_zero]
        exact ⟨implicationIdentity _ _⟩
      · simp only [List.Vector.get_cons_succ]
        exact ⟨liftK _ (.logical (.reflexive _))⟩)
  obtain ⟨u1⟩ := condTrans (recFormula tagL tagR tail) (liftK (recFormula tagL tagR tail) s1) cg
  obtain ⟨u2⟩ := condTrans (recFormula tagL tagR tail) u1 (liftK (recFormula tagL tagR tail) s2)
  obtain ⟨u3⟩ := condTrans (recFormula tagL tagR tail) u2 (liftK (recFormula tagL tagR tail) s3')
  have step : Derivation (Theory p) (.imp (recFormula tagL tagR tail)
      (GorbowStandardInduction.successorInstance (recFormula tagL tagR tail))) := by
    rw [phiSucc]
    exact u3
  -- The actual arithmetic induction instance, then instantiation at the head.
  have ind : Derivation (Theory p)
      (GorbowStandardInduction.inductionAxiom (recFormula tagL tagR tail)) :=
    .arithmetic (.induction (recFormula tagL tagR tail))
  have hall : Derivation (Theory p) (.all (recFormula tagL tagR tail)) :=
    .mp (.mp ind base) (.generalize step)
  have hfin : Derivation (Theory p)
      (GorbowStandardInstances.instantiate (recFormula tagL tagR tail) x) :=
    .mp (.logical (.allInstantiate (recFormula tagL tagR tail) x)) hall
  rw [phiInst] at hfin
  exact ⟨hfin⟩

/-! ### Registry coherence by structural induction on the common AST -/

private theorem coherent {n : Nat} (p : Program n) :
    ∀ {m : Nat} (q : Program m) (tagL tagR : Nat),
      (nodes p)[tagL]? = some ⟨m, q⟩ → (nodes p)[tagR]? = some ⟨m, q⟩ →
      ∀ ctx (args : List.Vector (Term ctx) m),
        Nonempty (Derivation (Theory p) (.equal (call tagL args) (call tagR args))) := by
  intro m q
  induction q with
  | zero =>
    intro tagL tagR hL hR ctx args
    obtain ⟨hl⟩ := zeroValue p tagL hL ctx args
    obtain ⟨hr⟩ := zeroValue p tagR hR ctx args
    obtain ⟨hs⟩ := eqSymm hr
    exact eqTrans hl hs
  | succ =>
    intro tagL tagR hL hR ctx args
    obtain ⟨hl⟩ := succValue p tagL hL ctx args
    obtain ⟨hr⟩ := succValue p tagR hR ctx args
    obtain ⟨hs⟩ := eqSymm hr
    exact eqTrans hl hs
  | projection i =>
    intro tagL tagR hL hR ctx args
    obtain ⟨hl⟩ := projectionValue p tagL i hL ctx args
    obtain ⟨hr⟩ := projectionValue p tagR i hR ctx args
    obtain ⟨hs⟩ := eqSymm hr
    exact eqTrans hl hs
  | @composition m k f g ihf ihg =>
    intro tagL tagR hL hR ctx args
    have hfL := GorbowPRSubtree.Proof.lookupTransport n p tagL ⟨m, .composition f g⟩ 1 ⟨k, f⟩ hL
      (GorbowPRChildTags.Proof.compositionFunction m k f g)
    have hfR := GorbowPRSubtree.Proof.lookupTransport n p tagR ⟨m, .composition f g⟩ 1 ⟨k, f⟩ hR
      (GorbowPRChildTags.Proof.compositionFunction m k f g)
    have hgL : ∀ i, (nodes p)[tagL + GorbowPRChildTags.argumentTag f g i]? = some ⟨m, g i⟩ :=
      fun i => GorbowPRSubtree.Proof.lookupTransport n p tagL ⟨m, .composition f g⟩
        (GorbowPRChildTags.argumentTag f g i) ⟨m, g i⟩ hL
        (GorbowPRChildTags.Proof.compositionArgument m k f g i)
    have hgR : ∀ i, (nodes p)[tagR + GorbowPRChildTags.argumentTag f g i]? = some ⟨m, g i⟩ :=
      fun i => GorbowPRSubtree.Proof.lookupTransport n p tagR ⟨m, .composition f g⟩
        (GorbowPRChildTags.argumentTag f g i) ⟨m, g i⟩ hR
        (GorbowPRChildTags.Proof.compositionArgument m k f g i)
    obtain ⟨eL⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tagL m k f g hL ctx args
    obtain ⟨eR⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tagR m k f g hR ctx args
    obtain ⟨c1⟩ := callCong (A := Theory p) (tagL + 1)
      (List.Vector.ofFn fun i => call (tagL + GorbowPRChildTags.argumentTag f g i) args)
      (List.Vector.ofFn fun i => call (tagR + GorbowPRChildTags.argumentTag f g i) args)
      (fun i => by
        simp only [List.Vector.get_ofFn]
        exact ihg i _ _ (hgL i) (hgR i) ctx args)
    obtain ⟨c2⟩ := ihf (tagL + 1) (tagR + 1) hfL hfR ctx
      (List.Vector.ofFn fun i => call (tagR + GorbowPRChildTags.argumentTag f g i) args)
    obtain ⟨eR'⟩ := eqSymm eR
    obtain ⟨t1⟩ := eqTrans eL c1
    obtain ⟨t2⟩ := eqTrans t1 c2
    exact eqTrans t2 eR'
  | @recursion k f g ihf ihg =>
    intro tagL tagR hL hR ctx args
    have hfL := GorbowPRSubtree.Proof.lookupTransport n p tagL ⟨k + 1, .recursion f g⟩ 1 ⟨k, f⟩ hL
      (GorbowPRChildTags.Proof.recursionBase k f g)
    have hfR := GorbowPRSubtree.Proof.lookupTransport n p tagR ⟨k + 1, .recursion f g⟩ 1 ⟨k, f⟩ hR
      (GorbowPRChildTags.Proof.recursionBase k f g)
    have hgL := GorbowPRSubtree.Proof.lookupTransport n p tagL ⟨k + 1, .recursion f g⟩
      (GorbowPRChildTags.stepTag f) ⟨k + 2, g⟩ hL (GorbowPRChildTags.Proof.recursionStep k f g)
    have hgR := GorbowPRSubtree.Proof.lookupTransport n p tagR ⟨k + 1, .recursion f g⟩
      (GorbowPRChildTags.stepTag f) ⟨k + 2, g⟩ hR (GorbowPRChildTags.Proof.recursionStep k f g)
    exact recursionCoherence p f g tagL tagR hL hR
      (fun ctx' v => ihf (tagL + 1) (tagR + 1) hfL hfR ctx' v)
      (fun ctx' v => ihg (tagL + GorbowPRChildTags.stepTag f) (tagR + GorbowPRChildTags.stepTag f)
        hgL hgR ctx' v) ctx args

theorem registryCoherence : GorbowPRInternalCoherence.Targets.RegistryCoherence := by
  intro n p tagL tagR m q hL hR ctx args
  exact coherent p q tagL tagR hL hR ctx args

theorem namedRegistryCoherence : GorbowPRInternalCoherence.Targets.NamedRegistryCoherence := by
  intro pF pR tagL tagR m q hL hR ctx args
  obtain ⟨d⟩ := coherent (GorbowSourceRegistryPadding.root pF pR) q tagL tagR hL hR ctx args
  exact GorbowTheoryProofProof.monotonicity _ (GorbowNamedDefiningTheory.Theory pF pR)
    (fun _ h => List.mem_append.mpr (Or.inl h)) ctx _ ⟨d⟩

/-! ### The specified two-copy registry -/

private theorem leftArgumentTag {n : Nat} (q : Program n) :
    GorbowPRChildTags.argumentTag (.projection (0 : Fin 2)) (fun _ : Fin 2 => q) 0 = leftTag := by
  unfold GorbowPRChildTags.argumentTag leftTag
  first
    | rfl
    | (simp only [List.ofFn_succ, List.ofFn_zero]; rfl)
    | simp [nodes]

private theorem rightArgumentTag {n : Nat} (q : Program n) :
    GorbowPRChildTags.argumentTag (.projection (0 : Fin 2)) (fun _ : Fin 2 => q) 1 =
      rightTag q := by
  unfold GorbowPRChildTags.argumentTag rightTag
  simp only [List.ofFn_succ, List.ofFn_zero]
  show 1 + 1 + (nodes q ++ []).length = 2 + (nodes q).length
  rw [List.append_nil]

theorem concreteDuplicate : GorbowPRInternalCoherence.Targets.ConcreteDuplicate := by
  intro n q
  have hl : (nodes (duplicateRoot q))[leftTag]? = some ⟨n, q⟩ := by
    have h := GorbowPRChildTags.Proof.compositionArgument n 2 (.projection (0 : Fin 2))
      (fun _ : Fin 2 => q) 0
    rw [leftArgumentTag] at h
    exact h
  have hr : (nodes (duplicateRoot q))[rightTag q]? = some ⟨n, q⟩ := by
    have h := GorbowPRChildTags.Proof.compositionArgument n 2 (.projection (0 : Fin 2))
      (fun _ : Fin 2 => q) 1
    rw [rightArgumentTag] at h
    exact h
  exact ⟨hl, hr, fun ctx args => coherent (duplicateRoot q) q leftTag (rightTag q) hl hr ctx args⟩

theorem fullTarget : GorbowPRInternalCoherence.Targets.Target :=
  ⟨openTermCongruence, conditionalTermCongruence, registryCoherence, namedRegistryCoherence,
    concreteDuplicate⟩

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.Proof
