module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax.Targets
/-- Exact literal BASE-term syntax roundtrip; variables/Phi/addition are not
replaced by arbitrary semantic observation fields. -/
def BaseSyntaxRoundtrip:Prop:=∀E:BaseTerm,BaseTerm.decode E.encode=E
/-- Exact source A_r syntax at every finite certificate level, including empty
head lists/sums and arbitrary positive coefficients and repeated subexpressions. -/
def CommonSyntaxRoundtrip:Prop:=∀n,∀E:CommonSyntax n,decodeCommon n (encodeCommon n E)=E
/-- The actual numeric coded syntax has the actual published source semantics
at EVERY shared raw valuation. Head values are computed by the proved code
algorithm; no fresh independent value is supplied for a child expression. -/
def ActualSourceCalibration:Prop:=∀Γ:List NONote,∀E:CommonSyntax Γ.length,∀ν:Nat→Nat,
  codedValue (headCodes Γ) (encodeCommon Γ.length E) ν=commonValue Γ E ν
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax.Targets
