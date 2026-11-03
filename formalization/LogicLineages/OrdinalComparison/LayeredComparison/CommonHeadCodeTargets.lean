module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Targets
open CommonHeadLargeGuards CommonHeadCompiler
/-- Numerical large-branch code is literal encoding of the accepted guard AST. -/
def LargeCodeExact : Prop:=∀ K cs desired,largeCode K cs desired=encode (largeFormula K cs desired)
/-- Numeric deletion code performs the actual original-index restoration. -/
def GuardCodeExact : Prop:=∀ i c p,guardedCode i c (encode p)=encode (CommonHeadGuardReindex.guarded i c p)
/-- Complete finite call tree has actual lower fuel; assembling its actual
child results gives the exact literal compiler, with no recursive-call oracle. -/
def RecursiveCodeEquation : Prop:=(∀a:Input,∀b∈children a,b.1<a.1)∧
  ∀a:Input,recursiveCode a=assemble a ((children a).map recursiveCode)
/-- Both numerical interfaces for the actual finite stack interpreter are
genuinely computable on all input codes. -/
def CodeInterfaces : Prop:=Computable children∧Computable₂ assemble
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode.Targets
