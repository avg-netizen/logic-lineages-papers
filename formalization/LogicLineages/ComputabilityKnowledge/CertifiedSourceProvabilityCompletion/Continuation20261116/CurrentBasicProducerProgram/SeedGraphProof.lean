module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SeedGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram CurrentRecursionBaseProgram.GraphPrimitives
theorem axiomGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : CurrentBasicProducerProgram.Installation p J)
 (raw : Program inputs) (rv : Term ctx) (hr : Computes p raw args rv) :
 Computes p (axiomProgram raw) args (axiomValue J rv) := by
 have hz := constantValue p args 0
 have hfour := constantValue p args 4
 have hpair := binary p args HistoryCodec.pair J.ptag I.hp
 have hargs := singletonGraph p args J.ctag I.hc raw rv hr
 exact singletonGraph p args J.ctag I.hc _ _
  (hpair _ _ _ _ hz (hpair _ _ _ _ hr (hpair _ _ _ _ hfour
   (hpair _ _ _ _ hz (hpair _ _ _ _ hargs (hpair _ _ _ _ hz hz))))))

theorem seedGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : CurrentBasicProducerProgram.Installation p J)
 (n : Nat) (f : Formula (n+1)) (raw : Fin (n+1) → Program inputs) (rv : List.Vector (Term ctx) (n+1))
 (hr : ∀ i, Computes p (raw i) args (rv.get i)) :
 Computes p (seedProgram n f raw) args (seedValue J n f rv) := by
 induction n with
 | zero => exact axiomGraph p args J I _ _ (quoteGraph p args f _ raw rv J.ctag J.atag I.hc I.ha hr)
 | succ n ih =>
  have ht : ∀ i : Fin (n+1), Computes p (raw i.succ) args (rv.tail.get i) := by
   intro i
   rw [List.Vector.get_tail_succ]
   exact hr i.succ
  have hh : Computes p (raw 0) args rv.head := by
   simpa only [List.Vector.get_zero] using hr 0
  exact mpGraph p args J.mtag I.hm _ _ _ _ _ _
   (quoteGraph p args f _ raw rv J.ctag J.atag I.hc I.ha hr)
   (allGraph p args J.ctag J.r13 I.hc I.h13 _ _ _ _
    (headGraph p args f (fun i => raw i.succ) rv.tail J.ctag J.atag I.hc I.ha ht) hh)
   (ih (.all f) (fun i => raw i.succ) rv.tail ht)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SeedGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SeedGraphProof
