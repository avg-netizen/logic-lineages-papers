module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler
open BalancedSyntax

/-- The actual ordinary BASE formula, defined structurally on the original
source shape. The leaf compares the actual BaseTerms. At each upper level,
the original finite box is FIRST and the translated original large guard is
SECOND. Every recursive lower comparison uses the same original C.1.

There is no supplied lower comparator, existential formula choice, decoder
extraction or semantic predicate in this definition. The noncomputable marker
comes from the accepted finite-box evaluation; the separately accepted raw
compiler supplies the exact all-code numerical construction. -/
noncomputable def typedFormula : (Γ : List Nat) → Certificate Γ →
    Syntax Γ → Syntax Γ → Int → BaseFormula.Formula
  | [], _, E, F, desired => BalancedRawCompiler.baseFormula E F desired
  | k :: Γ, C, E, F, desired =>
    .disjunction
      (BalancedBoxFormula.sourceFormula k Γ C E F desired)
      (BalancedGuardDescent.sourceTranslation k Γ C E F desired
        (fun G H d => typedFormula Γ C.1 G H d))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler
