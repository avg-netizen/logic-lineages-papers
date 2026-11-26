module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem successor {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a : Term ctx) :
 Computes p G .succ (a ::ᵥ nil) (.succ a) := by
 intro tag ht
 obtain ⟨h⟩ := Support.intoRegistry p .succ tag ht _ (NamedArithmeticGraph.Equations.successor tag ctx (a ::ᵥ nil))
 exact ⟨.base h⟩

theorem changeValue {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (q : Program arity)
 (args : List.Vector (Term ctx) arity) (a value : Term ctx)
 (ha : Computes p G q args a)
 (he : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal a value)) :
 Computes p G q args value := by
 intro tag ht
 obtain ⟨h⟩ := ha tag ht
 exact ⟨localTrans _ _ _ h he⟩

theorem headCons {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (t rest : Term ctx) :
 Computes p G HistoryLookup.head (HistoryLookup.consCall ctag t rest ::ᵥ nil) t := by
 intro tag ht
 obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx t rest
 exact ⟨.base h⟩

theorem tailCons {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (t rest : Term ctx) :
 Computes p G HistoryLookup.tail (HistoryLookup.consCall ctag t rest ::ᵥ nil) rest := by
 intro tag ht
 obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalTailCons n p tag ctag ht hc ctx t rest
 exact ⟨.base h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StepSupportProof
