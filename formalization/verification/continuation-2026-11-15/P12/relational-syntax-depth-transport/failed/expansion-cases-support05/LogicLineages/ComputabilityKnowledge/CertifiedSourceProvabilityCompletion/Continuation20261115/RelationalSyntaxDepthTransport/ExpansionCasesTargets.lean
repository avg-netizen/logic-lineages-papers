module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 ConstructorStepTargets
/-- Exactly six term and twelve formula constructors, in original token order. -/
def constructors : List Constructor :=
 [.term 0, .term 1, .term 2, .term 3, .term 4, .term 5,
  .formula 0, .formula 1, .formula 2, .formula 3, .formula 4, .formula 5,
  .formula 6, .formula 7, .formula 8, .formula 9, .formula 10, .formula 11]
/-- A successful constructor branch identifies original decoded kind, actual
runtime token and exact output prefix. No native decoded-task image is assumed. -/
def constructorCase {ctx : Nat} (ptag ctag l r : Nat) (task tok added : Term ctx)
 (ctor : Constructor) : Formula ctx :=
 .conj (.equal (call l (task ::ᵥ nil)) (Term.numeral (kind ctor)))
  (.conj (.equal tok (Term.numeral (token ctor)))
   (.equal added (FinitePrefixTargets.prefixTerm ctag (tasks ptag (call r (task ::ᵥ nil)) ctor))))
/-- The original index branch succeeds exactly on a positive bound-token
result; its returned task prefix is empty. This records an internal witness. -/
def indexCase {ctx : Nat} (dtag l r : Nat) (task tok added : Term ctx) : Formula ctx :=
 .conj (.equal (call l (task ::ᵥ nil)) (Term.numeral 2))
  (.conj (.ex (HistoryOrder.SupportProof.predBody
    (HistoryDifference.differenceCall dtag tok (call r (task ::ᵥ nil)))))
   (.equal added .zero))
/-- Finite original branch disjunction, with the index case as the final arm.
There is deliberately no native success predicate or malformed-code fallback. -/
def casesFormula {ctx : Nat} (ptag ctag dtag l r : Nat) (task tok added : Term ctx) : Formula ctx :=
 constructors.foldr (fun ctor rest => .disj (constructorCase ptag ctag l r task tok added ctor) rest)
  (indexCase dtag l r task tok added)
/-- Exhaustiveness for ALL original runtime task/token/output codes. In
particular malformed kind/token branches cannot satisfy the success premise.
All calls retain actual installed copies of the original programs. -/
def InternalExpansionSuccessCases : Prop := ∀ n (p : Program n) (etag ptag ctag dtag l r : Nat),
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (task tok added : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added))
   (casesFormula ptag ctag dtag l r task tok added)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesTargets
