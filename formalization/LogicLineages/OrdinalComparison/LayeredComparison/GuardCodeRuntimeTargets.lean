module
public import LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntimeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime.Targets
open CommonHeadCompiler CommonHeadLargeGuards CommonHeadLargeRow
/-- The actual numeric code runs to the actual Boolean guard value from
EVERY initial stack and has exactly the AST's original free-index list. -/
def ExactLiteralEncoding : Prop:=∀p:Formula,
  (∀ν stack,run ν (encode p) stack=boolValue ν p::stack)∧
  codeVariables (encode p)=p.variables∧∀ν,boolValue ν p=true↔p.eval ν
/-- ENTIRE source signed-row component: genuine ALL-code Computable compiler,
exact execution at EVERY genuine shared input valuation, no fresh index.
Raw certificate-layer translation and Snyatkov are deliberately separate. -/
def CompleteRowCode : Prop:=CommonHeadCompiler.Targets.AllCodeEffectivity∧
  (∀(rho:NONote),Order.IsSuccLimit rho.1.repr→∀ K cs desired (ν:Nat→Nat),
    (∀i<cs.length,actualOrdinalNorm rho.1.repr≤ν i)→
    (evaluate ν (compileCode (rawNoteEncode rho.1) K cs desired)=true↔
      Int.sign (value rho.1.repr K (inputRow cs ν))=desired))∧
  ∀h K cs desired,∀i∈codeVariables (compileCode h K cs desired),i<cs.length
end LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime.Targets
