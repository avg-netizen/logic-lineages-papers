module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

/-- Exact declared convention of foundations.tex: left combs everywhere,
except the explicitly parenthesized optional scalar box tail f+(g+n). -/
def defaultShape : (site : AdmissibleSum.MacroSite) → (n : Nat) → AdmissibleSum.Shape (n+1)
  | .optionalBoxTail, 2 => @AdmissibleSum.Shape.join 1 2 .leaf (@AdmissibleSum.Shape.join 1 1 .leaf .leaf)
  | _, n => leftShape n

def defaultPolicy : AdmissibleSum.Policy := ⟨defaultShape⟩
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
