module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerCompiler.Targets
open CommonLayerSyntax
/-- Actual encoded source expressions introduce NO new raw parameter in the
literal output code. The source grammar's same raw variable identity is kept. -/
def SourceCodeSupport:Prop:=∀Γ:List NONote,∀E F:CommonSyntax Γ.length,∀desired:Int,
  ∀i∈BaseFormula.rawVariables (CommonLayerComparison.compileCode (headCodes Γ)
    (encodeCommon Γ.length E) (encodeCommon Γ.length F) desired),
    i∈commonVariables Γ.length E++commonVariables Γ.length F
/-- Output is the code of an ACTUAL formula of the original BASE signature. -/
def LiteralOutputs:Prop:=∀Γ:List Nat,∀E F:Nat,∀desired:Int,∃p:BaseFormula.Formula,
  CommonLayerComparison.compileCode Γ E F desired=p.encode
/-- Entire original common-head syntax→literal BASE code compiler component.
Its numerical Computable clause is unconditional on ALL codes, and truth uses
ONE shared actual source valuation. This does NOT contain or assume Snyatkov
or quantified BASE decidability, so is NOT the entire source thm:common. -/
def CompleteLayerCompiler:Prop:=CommonLayerComparison.Targets.ExactCodedComparison∧
  CommonLayerComparison.Targets.ActualSourceComparison∧
  CommonLayerComparison.Targets.OriginalRawSupport∧
  CommonLayerComparison.Targets.AllCodeEffectivity∧SourceCodeSupport∧LiteralOutputs
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerCompiler.Targets
