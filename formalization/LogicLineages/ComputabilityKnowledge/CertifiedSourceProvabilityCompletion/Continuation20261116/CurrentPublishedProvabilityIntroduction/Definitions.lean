module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix
/-- Certificate coordinate first, then fuel, index, literal argument term, tag. -/
def bodyTemplate : Formula 5 :=
 .equal (CurrentRecursionBaseProgram.openCall (.var 4)
  (.var 2 ::ᵥ .var 1 ::ᵥ .zero ::ᵥ .var 3 ::ᵥ .var 0 ::ᵥ nil)) (.succ .zero)
def innerEnvironment : FixedFormulaSubstitution.Environment 5 1 4 :=
 Fin.cases (.inl 0) (fun i => .inr i)
def outerEnvironment : FixedFormulaSubstitution.Environment 4 1 3 :=
 Fin.cases (.inl 0) (fun i => .inr i)
/-- Inputs: numeric tag/index/fuel/certificate; RAW closed argument term;
RAW rho formula; input certificate. No post-selection tag is in this AST. -/
def quotedNumeral (i : Fin 7) : Program 7 := applyOne LiteralNumeralPrefix.numeralCode (.projection i)
def innerArguments : Fin 4 → Program 7 :=
 Fin.cases (quotedNumeral 2) (Fin.cases (quotedNumeral 1)
  (Fin.cases (.projection 4) (Fin.cases (quotedNumeral 0) Fin.elim0)))
def outerArguments : Fin 3 → Program 7 :=
 Fin.cases (quotedNumeral 1) (Fin.cases (.projection 4) (Fin.cases (quotedNumeral 0) Fin.elim0))
def innerMatrixProgram : Program 7 :=
 .composition (FixedFormulaSubstitution.formulaProgram bodyTemplate innerEnvironment) innerArguments
def outerMatrixProgram : Program 7 :=
 .composition (FixedFormulaSubstitution.formulaProgram (.ex bodyTemplate) outerEnvironment) outerArguments
def introduce {n : Nat} (matrix witness code : Program n) : Program n :=
 .composition CurrentExistentialIntroductionProgram.program (Fin.cases matrix (Fin.cases witness (Fin.cases code Fin.elim0)))
def innerProof : Program 7 := introduce innerMatrixProgram (quotedNumeral 3) (.projection 6)
def outerProof : Program 7 := introduce outerMatrixProgram (quotedNumeral 2) innerProof
def program : Program 7 :=
 CurrentRecursionStepProgram.liftProgram (FixedFormulaSubstitution.unary 11 outerMatrixProgram) (.projection 5) outerProof
/-- Exact original published predicate matrix, exposed only at its known outer
existential. The non-existential branch is irrelevant to the Native target. -/
def outerMatrix (pF : Program 1) (c : Code) (sigma : Sentence) : Formula 1 :=
 match prD pF c sigma with
 | .ex a => a
 | _ => .equal .zero .zero
def innerMatrix (pF : Program 1) (c : Code) (sigma : Sentence) (fuel : Nat) : Formula 1 :=
 match GorbowStandardInstances.instantiate (outerMatrix pF c sigma) (Term.numeral fuel) with
 | .ex a => a
 | _ => .equal .zero .zero
/-- Independent original two existential introductions and final K-lift,
with actual prD and rho, not a numerically equivalent replacement formula. -/
def number (pF : Program 1) (c : Code) (sigma : Sentence) (fuel certificate inputProof : Nat) : Nat :=
 CurrentImplicationCertificate.liftNumber (prD pF c sigma) (rho pF c)
  (CurrentExistentialIntroductionProgram.number (outerMatrix pF c sigma) (Term.numeral fuel)
   (CurrentExistentialIntroductionProgram.number (innerMatrix pF c sigma fuel) (Term.numeral certificate) inputProof))
def nativeInputs (pF : Program 1) (c : Code) (sigma : Sentence) (fuel certificate inputProof : Nat) : List.Vector Nat 7 :=
 GorbowNamedInternalProvability.checkerTag pF ::ᵥ Encodable.encode c ::ᵥ fuel ::ᵥ certificate ::ᵥ
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowBooleanTruth.binaryCodeTerm (n := 0) 0
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))) ::ᵥ
 Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c)) ::ᵥ inputProof ::ᵥ nil
/-- New fixed syntax and entire prior bundle precede the sole source selection. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨6,CurrentExistentialIntroductionProgram.extra f lhs rhs t rawOld ar baseX⟩,⟨7,program⟩]
/-- Exact checker equation's formula code with the LITERAL closed sorted
binaryCodeTerm in argument coordinate 3, not its numerical-value quotation. -/
def checkerEquationCode {ctx : Nat} (J : PrescribedRuntimeCallCongruence.Tags)
 (pF : Program 1) (c : Code) (sigma : Sentence) (fuel certificate : Term ctx) : Term ctx :=
 PrescribedRuntimeEquality.equalValue J.ctag J.atag
  (PrescribedRuntimeCallCongruence.callValue J (Term.numeral (GorbowNamedInternalProvability.checkerTag pF))
   (LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (Encodable.encode c)) ::ᵥ
    LiteralNumeralPrefix.numeralCall J.numeralTag fuel ::ᵥ
    LiteralNumeralPrefix.numeralCall J.numeralTag .zero ::ᵥ
    Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowBooleanTruth.binaryCodeTerm (n := 0) 0
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))) ::ᵥ
    LiteralNumeralPrefix.numeralCall J.numeralTag certificate ::ᵥ nil))
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ .zero))
def outputCode {ctx : Nat} (tag : Nat) (pF : Program 1) (c : Code) (sigma : Sentence)
 (fuel certificate inputProof : Term ctx) : Term ctx :=
 call tag (Term.numeral (GorbowNamedInternalProvability.checkerTag pF) ::ᵥ
  Term.numeral (Encodable.encode c) ::ᵥ fuel ::ᵥ certificate ::ᵥ
  Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowBooleanTruth.binaryCodeTerm (n := 0) 0
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))) ::ᵥ
  Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c))) ::ᵥ inputProof ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction
