module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.MultiplyProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.CircuitProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

inductive Circuit (arity : Nat) where
  | variable (i : Fin arity)
  | plus (a b : Circuit arity)
  | times (a b : Circuit arity)

def compile {arity : Nat} : Circuit arity → Program arity
  | .variable i => .projection i
  | .plus a b => binary add (compile a) (compile b)
  | .times a b => binary multiply (compile a) (compile b)

def term {arity ctx : Nat} (v : List.Vector (Term ctx) arity) : Circuit arity → Term ctx
  | .variable i => v.get i
  | .plus a b => .add (term v a) (term v b)
  | .times a b => .mul (term v a) (term v b)

private theorem binaryEquation {n arity ctx : Nat} (p : Program n) tag
    (op : Program 2) (f g : Program arity)
    (ht : (nodes p)[tag]? = some ⟨arity,binary op f g⟩)
    (v : List.Vector (Term ctx) arity) (a b : Term ctx)
    (hf : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+argumentTag op (Fin.cases g (Fin.cases f Fin.elim0)) 1) v) a)))
    (hg : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+argumentTag op (Fin.cases g (Fin.cases f Fin.elim0)) 0) v) b))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag v) (call (tag+1) (b ::ᵥ a ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag op
    (Fin.cases g (Fin.cases f Fin.elim0)) ht v (b ::ᵥ a ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact hg
  | succ i => cases i using Fin.cases with
    | zero => exact hf
    | succ i => exact Fin.elim0 i

theorem circuitEquation {arity : Nat} (c : Circuit arity) :
    ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨arity,compile c⟩ →
    ∀ ctx (v : List.Vector (Term ctx) arity),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag v) (term v c))) := by
  induction c with
  | «variable» i =>
      intro n p tag ht ctx v
      exact SixSol20261112.Fuel.Equations.projection p tag i ht v
  | plus a b ha hb =>
      intro n p tag ht ctx v
      let args : Fin 2 → Program arity := Fin.cases (compile b) (Fin.cases (compile a) Fin.elim0)
      have hf := SixSol20261112.Fuel.Equations.functionChild p tag add args ht
      have hleft := SixSol20261112.Fuel.Equations.argumentChild p tag add args ht 1
      have hright := SixSol20261112.Fuel.Equations.argumentChild p tag add args ht 0
      obtain ⟨hc⟩ := binaryEquation p tag add (compile a) (compile b) ht v
        (term v a) (term v b) (ha n p _ hleft ctx v) (hb n p _ hright ctx v)
      obtain ⟨ho⟩ := AddProof.internalAdd n p (tag+1) hf ctx (term v b) (term v a)
      exact ⟨Logic.trans _ _ _ hc ho⟩
  | times a b ha hb =>
      intro n p tag ht ctx v
      let args : Fin 2 → Program arity := Fin.cases (compile b) (Fin.cases (compile a) Fin.elim0)
      have hf := SixSol20261112.Fuel.Equations.functionChild p tag multiply args ht
      have hleft := SixSol20261112.Fuel.Equations.argumentChild p tag multiply args ht 1
      have hright := SixSol20261112.Fuel.Equations.argumentChild p tag multiply args ht 0
      obtain ⟨hc⟩ := binaryEquation p tag multiply (compile a) (compile b) ht v
        (term v a) (term v b) (ha n p _ hleft ctx v) (hb n p _ hright ctx v)
      obtain ⟨ho⟩ := MultiplyProof.internalMultiply n p (tag+1) hf ctx (term v b) (term v a)
      exact ⟨Logic.trans _ _ _ hc ho⟩

theorem highEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,high⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.add (.add (.mul a a) a) b))) :=
  circuitEquation (.plus (.plus (.times (.variable 0) (.variable 0)) (.variable 0)) (.variable 1))
    n p tag ht ctx (a ::ᵥ b ::ᵥ nil)

theorem lowEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,low⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.add (.mul b b) a))) :=
  circuitEquation (.plus (.times (.variable 1) (.variable 1)) (.variable 0))
    n p tag ht ctx (a ::ᵥ b ::ᵥ nil)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.CircuitProof
