module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula
open BalancedSyntax

abbrev Code := List CommonHeadCompiler.Instruction
abbrev Input := Nat × List Nat × Nat × Nat × Nat × Int

/-- Literal Boolean folds in the EXISTING BASE syntax. The empty point is
true, and a finite disjunction with no retained points is false. -/
def conjunction (ps : List BaseFormula.Formula) : BaseFormula.Formula :=
  ps.foldr BaseFormula.Formula.conjunction .truth

def disjunction (ps : List BaseFormula.Formula) : BaseFormula.Formula :=
  ps.foldr BaseFormula.Formula.disjunction .falsity

/-- Coordinate positions enumerate the original ordered support. Atomic
operands are literal raw variables and numeral terms, not independently
valued basis entries or an added equality predicate. -/
def pointFormula (support word : List Nat) : BaseFormula.Formula :=
  conjunction ((List.range support.length).map (fun j =>
    .equal (.variable (support.getD j 0)) (.numeral (word.getD j 1))))

/-- The existing postfix instruction language, with ACTUAL BaseTerm codes:
variable i has code 4*i+1 and numeral v has code 4*v. -/
def pointCode (support word : List Nat) : Code :=
  CommonHeadCode.conjoin ((List.range support.length).map (fun j =>
    [(2, 4 * support.getD j 0 + 1, 4 * word.getD j 1)]))

/-- Exactly the original raw pair support, extracted by the unchanged
source-code algorithm before any sign filtering or block collection. Only
repeated raw names are removed; certificate basis entries are untouched. -/
def rawSupport (k : Nat) (Γ : List Nat) (C E F : Nat) : List Nat :=
  (BalancedEvaluation.codeVariables (k :: Γ) C E ++
    BalancedEvaluation.codeVariables (k :: Γ) C F).dedup

/-- The existing positive word enumeration at the ORIGINAL signed-row
threshold. No enlarged bound, alternative enumeration or small-input filter. -/
noncomputable def rawWords (k : Nat) (Γ : List Nat) (C E F : Nat) : List (List Nat) :=
  singleCoreBoxWords (BalancedSourceAdapter.threshold k E F)
    (rawSupport k Γ C E F).length

/-- The genuine existing joint evaluator supplies both natural values at
the SAME concrete finite raw table. Subtraction is in Int, not truncated Nat.
The complete-input list is neither reevaluated nor used as another filter. -/
noncomputable def codeSign (shape : List Nat) (C E F : Nat)
    (support word : List Nat) : Int :=
  let table := BalancedBoxEvaluation.finiteTable support word
  Int.sign (((BalancedEvaluation.joint (shape, C, E, table)).1 : Int) -
    ((BalancedEvaluation.joint (shape, C, F, table)).1 : Int))

noncomputable def sourceSign (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (word : List Nat) : Int :=
  codeSign (k :: Γ) (BalancedEvaluation.encodeCertificate (k :: Γ) C)
    (BalancedEvaluation.encodeSyntax (k :: Γ) E)
    (BalancedEvaluation.encodeSyntax (k :: Γ) F)
    (BalancedSmallBox.sourceSupport k Γ C E F) word

/-- Retain EVERY correctly evaluated point of the original finite box with
the requested sign. A separate some-input-small test is unnecessary for
soundness; the accepted small-box bound supplies small-branch completeness.
Outside raw names do not occur in any point clause. -/
noncomputable def sourceFormula (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (desired : Int) : BaseFormula.Formula :=
  disjunction (((BalancedSmallBox.boxWords k Γ C E F).filter
    (fun word => decide (sourceSign k Γ C E F word = desired))).map
      (pointFormula (BalancedSmallBox.sourceSupport k Γ C E F)))

/-- Uniform raw-source numeric output using the SAME support extraction,
original-threshold algorithm, box words, finite table and joint sign test.
This produces only literal BASE postfix code, with no evaluator opcode. -/
noncomputable def formulaCode (k : Nat) (Γ : List Nat) (C E F : Nat)
    (desired : Int) : Code :=
  let support := rawSupport k Γ C E F
  CommonHeadCode.disjoin (((rawWords k Γ C E F).filter
    (fun word => decide (codeSign (k :: Γ) C E F support word = desired))).map
      (pointCode support))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula
