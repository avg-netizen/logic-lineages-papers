module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Exactly the original valid constructor-token families. Index tasks and
arbitrary malformed kind/token codes are not covered by this finite family. -/
inductive Constructor where
 | term : Fin 6 → Constructor
 | formula : Fin 12 → Constructor
def kind : Constructor → Nat
 | .term _ => 0
 | .formula _ => 1
def token : Constructor → Nat
 | .term i => i.val
 | .formula i => i.val
/-- Literal expansion rows from original termBranch/formulaBranch; elements are
runtime task terms, including capture-bound increment for tokens10/11. -/
def tasks {ctx : Nat} (ptag : Nat) (binder : Term ctx) : Constructor → List (Term ctx)
 | .term i =>
  match i.val with
  | 0 => [LiteralSyntaxStep.taskCall ptag 2 binder]
  | 1 => []
  | 2 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 3 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 4 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | _ => [LiteralSyntaxStep.taskCall ptag 0 binder]
 | .formula i =>
  match i.val with
  | 0 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 1 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 2 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 3 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 4 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 5 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 6 => [LiteralSyntaxStep.taskCall ptag 1 binder]
  | 7 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | 8 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | 9 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | _ => [LiteralSyntaxStep.taskCall ptag 1 (.succ binder)]
def output {ctx : Nat} (ptag ctag atag : Nat) (ctor : Constructor) (binder rest : Term ctx) : Term ctx :=
 HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder ctor)) rest
def input {ctx : Nat} (ptag ctag : Nat) (ctor : Constructor) (binder rest : Term ctx) : Term ctx :=
 .succ (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) binder) rest)
/-- Every valid finite constructor branch of the actual original step AST,
with both step equations and related output stacks derived internally.
No expansion equation, dispatcher calibration or step simulation is a premise. -/
def InternalConstructorStepPair : Prop := ∀ n (p : Program n) stag etag ptag ctag atag len q l r,
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ →
 (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
 (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩ →
 (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (ctor : Constructor) (oldBound newBound rest newRest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (HistoryBounds.weakBound oldBound newBound)
   (.imp (stackRelation len q l r rest newRest)
    (.conj
     (.equal (LiteralSyntaxStep.stepCall stag (input ptag ctag ctor oldBound rest) (Term.numeral (token ctor)))
      (.succ (output ptag ctag atag ctor oldBound rest)))
     (.conj
      (.equal (LiteralSyntaxStep.stepCall stag (input ptag ctag ctor newBound newRest) (Term.numeral (token ctor)))
       (.succ (output ptag ctag atag ctor newBound newRest)))
      (stackRelation len q l r (output ptag ctag atag ctor oldBound rest)
       (output ptag ctag atag ctor newBound newRest)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepTargets
