module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

def Computes {n arity ctx : Nat} (p : Program n) (q : Program arity) (args : List.Vector (Term ctx) arity) (value : Term ctx) : Prop :=
  ∀ tag, (nodes p)[tag]? = some ⟨arity,q⟩ → Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) value))
theorem projection {n arity ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity) (i : Fin arity) :
    Computes p (.projection i) args (args.get i) := fun tag ht => SixSol20261112.Fuel.Equations.projection p tag i ht args

theorem binary {n arity ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity)
    (f : Program 2) (ftag : Nat) (hf : (nodes p)[ftag]? = some ⟨2,f⟩)
    (a b : Program arity) (av bv : Term ctx) (ha : Computes p a args av) (hb : Computes p b args bv) :
    Computes p (applyTwo f a b) args (call ftag (av ::ᵥ bv ::ᵥ nil)) := by
  intro tag ht
  let g := Fin.cases a (Fin.cases b Fin.elim0)
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.binaryValues p tag f g ht args av bv
    (ha _ (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht 0))
    (hb _ (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht 1))
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tag+1) ftag 2 f
    (SixSol20261112.Fuel.Equations.functionChild p tag f g ht) hf ctx (av ::ᵥ bv ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ he hcopy⟩

theorem unary {n arity ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity)
    (f : Program 1) (ftag : Nat) (hf : (nodes p)[ftag]? = some ⟨1,f⟩)
    (a : Program arity) (av : Term ctx) (ha : Computes p a args av) :
    Computes p (applyOne f a) args (call ftag (av ::ᵥ nil)) := by
  intro tag ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag f (fun _ => a) ht args av
    (ha _ (SixSol20261112.Fuel.Equations.argumentChild p tag f (fun _ => a) ht 0))
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tag+1) ftag 1 f
    (SixSol20261112.Fuel.Equations.functionChild p tag f (fun _ => a) ht) hf ctx (av ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ he hcopy⟩

theorem constantValue {n arity ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity) (k : Nat) :
    Computes p (constant arity k) args (Term.numeral k) := by
  induction k with
  | zero => intro tag ht; exact HistoryAppend.TableEquationsProof.zeroEquation p tag ht args
  | succ k ih =>
    intro tag ht
    obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag .succ (fun _ => constant arity k) ht args (Term.numeral k)
      (ih _ (SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ => constant arity k) ht 0))
    obtain ⟨hs⟩ := Support.intoRegistry p .succ (tag+1)
      (SixSol20261112.Fuel.Equations.functionChild p tag .succ (fun _ => constant arity k) ht) _
      (NamedArithmeticGraph.Equations.successor (tag+1) ctx (Term.numeral k ::ᵥ nil))
    exact ⟨Logic.trans _ _ _ he hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
