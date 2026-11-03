module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Targets
open CommonLayerSyntax
/-- Every numeric expression code, every original common-head layer, every
signed requested answer and every SHARED actual raw valuation. No independent
input values, closed-value oracle, omitted small exceptions or solver premise. -/
def ExactCodedComparison:Prop:=∀Γ:List NONote,genuineHeads Γ→
  ∀E F:Nat,∀desired:Int,∀ν:Nat→Nat,
  (compile (headCodes Γ) E F desired).eval ν↔
    Int.sign ((codedValue (headCodes Γ) E ν:Int)-(codedValue (headCodes Γ) F ν:Int))=desired
/-- Literal source Ar expressions, with one ambient original raw assignment. -/
def ActualSourceComparison:Prop:=∀Γ:List NONote,genuineHeads Γ→
  ∀E F:CommonSyntax Γ.length,∀desired:Int,∀ν:Nat→Nat,
  BaseFormula.evaluate ν (compileCode (headCodes Γ)
    (encodeCommon Γ.length E) (encodeCommon Γ.length F) desired)=true↔
    Int.sign ((commonValue Γ E ν:Int)-(commonValue Γ F ν:Int))=desired
/-- No fresh raw variable is introduced by term decoding or guard substitution. -/
def OriginalRawSupport:Prop:=∀Γ:List Nat,∀E F:Nat,∀desired:Int,
  ∀i∈(compile Γ E F desired).variables,
    i∈codedVariables Γ.length E++codedVariables Γ.length F
/-- Actual uniformly computable code output on ALL head/expression/sign codes.
This remains a distinct proof obligation from mathematical recursion. -/
def AllCodeEffectivity:Prop:=Computable (fun p:List Nat×Nat×Nat×Int=>
  compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Targets
