module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.IndependenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

/-- A syntactic certificate only: the source's history input is unused.
Composition may use any actual function Program, but every input to it must
itself have this certificate. No semantic/native invariance premise occurs. -/
inductive Independent : Program 4 → Prop
  | projection (i : Fin 4) (hne : i ≠ 2) : Independent (.projection i)
  | composition {k : Nat} (f : Program k) (g : Fin k → Program 4)
      (children : ∀ i, Independent (g i)) : Independent (.composition f g)

def args {ctx : Nat} (index fuel h line : Term ctx) : List.Vector (Term ctx) 4 :=
  index ::ᵥ fuel ::ᵥ h ::ᵥ line ::ᵥ nil

theorem projected {ctx : Nat} (i : Fin 4) (hne : i ≠ 2) (index fuel h h' line : Term ctx) :
    (args index fuel h line).get i = (args index fuel h' line).get i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => exact False.elim (hne rfl)
      | succ i => cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i

theorem independentEquation {q : Program 4} (hq : Independent q) :
    ∀ arity (p : Program arity) tag, (nodes p)[tag]? = some ⟨4,q⟩ →
    ∀ ctx (index fuel h h' line : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (args index fuel h line)) (call tag (args index fuel h' line)))) := by
  induction hq with
  | projection i hne =>
      intro arity p tag ht ctx index fuel h h' line
      obtain ⟨ha⟩ := SixSol20261112.Fuel.Equations.projection p tag i ht (args index fuel h line)
      obtain ⟨hb⟩ := SixSol20261112.Fuel.Equations.projection p tag i ht (args index fuel h' line)
      rw [projected i hne index fuel h h' line] at ha
      exact ⟨Logic.trans _ _ _ ha (Support.equalitySymmetry _ _ hb)⟩
  | composition f g children ih =>
      intro arity p tag ht ctx index fuel h h' line
      obtain ⟨ha⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation arity p tag 4 _ f g ht ctx (args index fuel h line)
      obtain ⟨hb⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation arity p tag 4 _ f g ht ctx (args index fuel h' line)
      have hc := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) (tag+1)
        (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (args index fuel h line))
        (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (args index fuel h' line))
        (fun i => by
          simpa only [List.Vector.get_ofFn] using Classical.choice
            (ih i arity p _ (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht i)
              ctx index fuel h h' line))
      exact ⟨Logic.trans _ _ _ ha (Logic.trans _ _ _ hc (Support.equalitySymmetry _ _ hb))⟩

theorem unary {q : Program 4} (f : Program 1) (h : Independent q) : Independent (applyOne f q) :=
  .composition f (fun _ => q) (fun _ => h)
theorem binary {a b : Program 4} (f : Program 2) (ha : Independent a) (hb : Independent b) :
    Independent (applyTwo f a b) := by
  apply Independent.composition
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => cases i using Fin.cases with
    | zero => exact hb
    | succ i => exact Fin.elim0 i

theorem chooseIndependent {t a b : Program 4} (ht : Independent t) (ha : Independent a) (hb : Independent b) :
    Independent (choose t a b) := by
  apply Independent.composition
  intro i
  cases i using Fin.cases with
  | zero => exact ht
  | succ i => cases i using Fin.cases with
    | zero => exact ha
    | succ i => cases i using Fin.cases with
      | zero => exact hb
      | succ i => exact Fin.elim0 i

theorem constantIndependent (k : Nat) : Independent (constant 4 k) := by
  induction k with
  | zero => exact .composition .zero Fin.elim0 (fun i => Fin.elim0 i)
  | succ k ih => exact unary .succ ih

theorem lineIndependent : Independent lineCode := .projection 3 (by decide)
theorem leftIndependent {q : Program 4} (h : Independent q) : Independent (left q) := unary _ h
theorem rightIndependent {q : Program 4} (h : Independent q) : Independent (right q) := unary _ h

theorem contextIndependent : Independent contextCode := leftIndependent lineIndependent
theorem rawIndependent : Independent rawCode := leftIndependent (rightIndependent lineIndependent)
theorem ruleIndependent : Independent ruleCode := leftIndependent (rightIndependent (rightIndependent lineIndependent))
theorem payloadIndependent : Independent payloadCode := rightIndependent (rightIndependent (rightIndependent lineIndependent))
theorem tagIndependent : Independent payloadTag := leftIndependent payloadIndependent
theorem argsIndependent : Independent payloadArgs := leftIndependent (rightIndependent payloadIndependent)
theorem ref1Independent : Independent ref1 := leftIndependent (rightIndependent (rightIndependent payloadIndependent))
theorem ref2Independent : Independent ref2 := rightIndependent (rightIndependent (rightIndependent payloadIndependent))
theorem zeroIndependent {q : Program 4} (hq : Independent q) : Independent (zeroTest q) := binary _ hq (constantIndependent 0)
theorem conjunctionIndependent {a b : Program 4} (ha : Independent a) (hb : Independent b) :
    Independent (conjunction a b) := chooseIndependent ha (constantIndependent 0) hb

theorem commonIndependent : Independent commonGuard := conjunctionIndependent (zeroIndependent tagIndependent) (zeroIndependent argsIndependent)
theorem generalizeIndependent : Independent generalizeGuard := conjunctionIndependent commonIndependent (zeroIndependent ref2Independent)
theorem ruleTestIndependent (r : Nat) : Independent (applyTwo equalCode ruleCode (constant 4 r)) := binary _ ruleIndependent (constantIndependent r)
theorem unaryLeafIndependent (q : Program 1) : Independent (applyOne q lineCode) := unary _ lineIndependent

theorem axiomIndependent (q : Program 3) : Independent (.composition q axiomArguments) := by
  apply Independent.composition
  intro i
  cases i using Fin.cases with
  | zero => exact .projection 0 (by decide)
  | succ i => cases i using Fin.cases with
    | zero => exact .projection 1 (by decide)
    | succ i => cases i using Fin.cases with
      | zero => exact lineIndependent
      | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.IndependenceProof
