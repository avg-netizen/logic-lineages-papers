module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompilerTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof

@[expose] public section
/-! Correctness of the literal structural compiler for arithmetic templates.
External evaluation is structural induction on the template. Internally, every
occurrence of a compiled AST is reduced by its actual node and composition
equations at actual child tags, with the paid internal addition and
multiplication at the function child; substitution arguments are arbitrary
terms. The source header template is arithmetic, and its compiled occurrence
proves the exact source `headerTerm`. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.Proof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowPRRegistry GorbowSubstitution
open GorbowPRDefiningEquations (call argumentVariables nodeEquations)
open GorbowPRNumeralCalculation (Theory)
open List.Vector

/-! ### External evaluation -/

private theorem evalCompile {n : Nat} (t : Term n) : arithmetic t →
    ∀ (v : List.Vector Nat n) (I : Interpretation), evaluate (compile t) v = t.realize I v.get := by
  induction t with
  | var i => intro _ v I; rfl
  | zero => intro _ v I; rfl
  | succ t ih =>
    intro ht v I
    have hv : (List.Vector.ofFn fun _ : Fin 1 => evaluate (compile t) v) =
        evaluate (compile t) v ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      rw [List.Vector.get_ofFn]
      obtain rfl : i = 0 := Fin.eq_zero i
      rfl
    show Nat.succ (List.Vector.ofFn fun _ : Fin 1 => evaluate (compile t) v).head =
      Nat.succ (t.realize I v.get)
    rw [hv, List.Vector.head_cons, ih ht v I]
  | add t u iht ihu =>
    intro ht v I
    have hv : (List.Vector.ofFn fun i : Fin 2 =>
        evaluate ((Fin.cases (compile u) (fun _ : Fin 1 => compile t) : Fin 2 → Program n) i) v) =
        evaluate (compile u) v ::ᵥ evaluate (compile t) v ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      rw [List.Vector.get_ofFn]
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · obtain rfl : j = 0 := Fin.eq_zero j
        rfl
    show evaluate GorbowPRInternalArithmetic.addition (List.Vector.ofFn fun i : Fin 2 =>
        evaluate ((Fin.cases (compile u) (fun _ : Fin 1 => compile t) : Fin 2 → Program n) i) v) =
      t.realize I v.get + u.realize I v.get
    rw [hv, GorbowPRInternalArithmetic.Proof.actualEvaluation.1, iht ht.1 v I, ihu ht.2 v I]
  | mul t u iht ihu =>
    intro ht v I
    have hv : (List.Vector.ofFn fun i : Fin 2 =>
        evaluate ((Fin.cases (compile u) (fun _ : Fin 1 => compile t) : Fin 2 → Program n) i) v) =
        evaluate (compile u) v ::ᵥ evaluate (compile t) v ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      rw [List.Vector.get_ofFn]
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · obtain rfl : j = 0 := Fin.eq_zero j
        rfl
    show evaluate GorbowPRInternalArithmetic.multiplication (List.Vector.ofFn fun i : Fin 2 =>
        evaluate ((Fin.cases (compile u) (fun _ : Fin 1 => compile t) : Fin 2 → Program n) i) v) =
      t.realize I v.get * u.realize I v.get
    rw [hv, GorbowPRInternalArithmetic.Proof.actualEvaluation.2.1, iht ht.1 v I, ihu ht.2 v I]
  | universalFunction t ih =>
    intro ht
    exact (ht : False).elim

theorem actualEvaluation : GorbowArithmeticTermCompiler.Targets.ActualEvaluation := by
  intro n t ht v I
  exact evalCompile t ht v I

/-! ### Equality transitivity in arbitrary contexts -/

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

private theorem eqTrans {A : Sentence → Prop} {ctx : Nat} {a b c : Term ctx}
    (h1 : Derivation A (.equal a b)) (h2 : Derivation A (.equal b c)) :
    Nonempty (Derivation A (.equal a c)) := by
  have e : Derivation A (.imp (.equal b c)
      (.imp (GorbowStandardInstances.instantiate (.equal (shift a) (.var 0)) b)
        (GorbowStandardInstances.instantiate (.equal (shift a) (.var 0)) c))) :=
    .logical (.equalityReplace (.equal (shift a) (.var 0)) b c)
  rw [instShiftEqual, instShiftEqual] at e
  exact ⟨.mp (.mp e h2) h1⟩

/-! ### Call congruence, node values and child lookups -/

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

/-! ### Internal compiler correctness -/

private theorem compileCorrect {n : Nat} (t : Term n) : arithmetic t →
    ∀ m (p : Program m) tag, (nodes p)[tag]? = some ⟨n, compile t⟩ →
    ∀ ctx (σ : Fin n → Term ctx),
      Nonempty (Derivation (Theory p)
        (.equal (call tag (List.Vector.ofFn σ)) (substitute σ t))) := by
  induction t with
  | var i =>
    intro _ m p tag h ctx σ
    obtain ⟨d⟩ := projectionValue p tag i h ctx (List.Vector.ofFn σ)
    rw [List.Vector.get_ofFn] at d
    exact ⟨d⟩
  | zero =>
    intro _ m p tag h ctx σ
    have hf := compFunLookup p tag .zero (Fin.elim0 : Fin 0 → Program n) h
    obtain ⟨c⟩ := compValue p tag .zero (Fin.elim0 : Fin 0 → Program n) h ctx
      (List.Vector.ofFn σ) List.Vector.nil (fun i => Fin.elim0 i)
    obtain ⟨z⟩ := zeroValue p (tag + 1) hf ctx List.Vector.nil
    exact eqTrans c z
  | succ t ih =>
    intro ht m p tag h ctx σ
    have hf := compFunLookup p tag .succ (fun _ : Fin 1 => compile t) h
    obtain ⟨c⟩ := compValue p tag .succ (fun _ : Fin 1 => compile t) h ctx
      (List.Vector.ofFn σ) (substitute σ t ::ᵥ List.Vector.nil)
      (fun i => by
        obtain rfl : i = 0 := Fin.eq_zero i
        exact ih ht m p _ (compArgLookup p tag .succ (fun _ : Fin 1 => compile t) h 0) ctx σ)
    obtain ⟨s⟩ := succValue p (tag + 1) hf ctx (substitute σ t ::ᵥ List.Vector.nil)
    exact eqTrans c s
  | add t u iht ihu =>
    intro ht m p tag h ctx σ
    have hf := compFunLookup p tag GorbowPRInternalArithmetic.addition
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h
    obtain ⟨c⟩ := compValue p tag GorbowPRInternalArithmetic.addition
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h ctx
      (List.Vector.ofFn σ) (substitute σ u ::ᵥ substitute σ t ::ᵥ List.Vector.nil)
      (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ihu ht.2 m p _
            (compArgLookup p tag GorbowPRInternalArithmetic.addition
              (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h 0) ctx σ
        · obtain rfl : j = 0 := Fin.eq_zero j
          exact iht ht.1 m p _
            (compArgLookup p tag GorbowPRInternalArithmetic.addition
              (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h (Fin.succ 0)) ctx σ)
    obtain ⟨a⟩ := GorbowPRInternalArithmetic.Proof.internalAddition m p (tag + 1) hf ctx
      (substitute σ t) (substitute σ u)
    exact eqTrans c a
  | mul t u iht ihu =>
    intro ht m p tag h ctx σ
    have hf := compFunLookup p tag GorbowPRInternalArithmetic.multiplication
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h
    obtain ⟨c⟩ := compValue p tag GorbowPRInternalArithmetic.multiplication
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h ctx
      (List.Vector.ofFn σ) (substitute σ u ::ᵥ substitute σ t ::ᵥ List.Vector.nil)
      (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ihu ht.2 m p _
            (compArgLookup p tag GorbowPRInternalArithmetic.multiplication
              (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h 0) ctx σ
        · obtain rfl : j = 0 := Fin.eq_zero j
          exact iht ht.1 m p _
            (compArgLookup p tag GorbowPRInternalArithmetic.multiplication
              (Fin.cases (compile u) (fun _ : Fin 1 => compile t)) h (Fin.succ 0)) ctx σ)
    obtain ⟨a⟩ := GorbowPRInternalArithmetic.Proof.internalMultiplication m p (tag + 1) hf ctx
      (substitute σ t) (substitute σ u)
    exact eqTrans c a
  | universalFunction t ih =>
    intro ht
    exact (ht : False).elim

theorem internalCompiler : GorbowArithmeticTermCompiler.Targets.InternalCompiler := by
  intro n t ht m p tag h ctx σ
  exact compileCorrect t ht m p tag h ctx σ

/-! ### The source header template is arithmetic -/

private theorem arithNumeral {n : Nat} : ∀ k : Nat, arithmetic (Term.numeral k : Term n)
  | 0 => trivial
  | k + 1 => arithNumeral (n := n) k

private theorem arithPair {n : Nat} {a b : Term n} (ha : arithmetic a) (hb : arithmetic b) :
    arithmetic (GorbowRegistryTuple.pairTerm a b) :=
  ⟨⟨⟨ha, hb⟩, ⟨ha, hb⟩⟩, ha⟩

private theorem arithTuple {n : Nat} :
    ∀ as : List (Term n), (∀ a ∈ as, arithmetic a) →
      arithmetic (GorbowRegistryTuple.tupleTerm as)
  | [], _ => trivial
  | a :: as, h =>
    arithPair (h a (List.mem_cons_self ..)) (arithTuple as (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem arithVariables (arity : Nat) :
    ∀ a ∈ (argumentVariables arity).toList, arithmetic a := by
  intro a ha
  simp only [argumentVariables, List.Vector.toList_ofFn, List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  trivial

theorem headerCoverage : GorbowArithmeticTermCompiler.Targets.HeaderCoverage := by
  intro arity tag
  exact arithPair (arithNumeral arity) (arithPair (arithNumeral tag)
    (arithTuple _ (arithVariables arity)))

/-! ### Internal source headers -/

private theorem headerSub {ctx : Nat} (arity tag : Nat) (args : List.Vector (Term ctx) arity) :
    substitute args.get (headerTemplate arity tag) =
      GorbowRegistryTuple.headerTerm arity tag args.toList := by
  unfold headerTemplate
  rw [GorbowHeaderSubstitutionProof.headers, ← List.Vector.toList_map, sub_arguments]

theorem internalHeaders : GorbowArithmeticTermCompiler.Targets.InternalHeaders := by
  intro arity sourceTag m p registryTag h ctx args
  obtain ⟨d⟩ := compileCorrect (headerTemplate arity sourceTag) (headerCoverage arity sourceTag)
    m p registryTag h ctx args.get
  rw [List.Vector.ofFn_get, headerSub] at d
  exact ⟨d⟩

theorem fullTarget : GorbowArithmeticTermCompiler.Targets.Target :=
  ⟨actualEvaluation, internalCompiler, headerCoverage, internalHeaders⟩

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.Proof
