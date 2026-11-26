module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence CurrentImplicationCertificate CurrentEqualityImplication

/-- Literal second original node equation; no reassociated equation. -/
def rootFormula {m : Nat} (f : Program m) (tag : Nat) : Formula (m+1) :=
 .equal (call tag (.succ (.var 0) ::ᵥ tailVariables m))
  (call (tag+stepTag f) (.var 0 ::ᵥ call tag (.var 0 ::ᵥ tailVariables m) ::ᵥ tailVariables m))
/-- Protected coordinate0 is the accumulator. Closed runtime coordinates
are counter then original input values. -/
def stepEnvironment (m : Nat) : FixedFormulaSubstitution.Environment (m+2) 1 (m+1) :=
 Fin.cases (.inl 0) (fun i => .inr i)
def stepTemplate (m tag : Nat) : Term (m+2) :=
 call tag (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.ofFn (fun i : Fin m => .var i.succ.succ))
def closedStepFunction {m : Nat} (tag counter : Nat) (inputs : List.Vector Nat m) : Term 1 :=
 call tag ((Term.numeral counter : Term 1) ::ᵥ .var 0 ::ᵥ
  (GorbowPRNumeralCalculation.numeralArguments inputs).map (GorbowClosedEquality.liftClosedTerm 1))
/-- Original ordinary implication recipe. Only the step-child certificate is
an input number. No previous calculation certificate is consumed. -/
def number {m : Nat} (f : Program m) (tag counter : Nat) (inputs : List.Vector Nat m)
 (previous result childCode : Nat) : Nat :=
 let av := GorbowPRNumeralCalculation.numeralArguments inputs
 let priorCall := call tag (Term.numeral counter ::ᵥ av)
 let priorNum := Term.numeral previous
 let nextCall := call tag (Term.numeral (counter+1) ::ᵥ av)
 let left := call (tag+stepTag f) (Term.numeral counter ::ᵥ priorCall ::ᵥ av)
 let right := call (tag+stepTag f) (Term.numeral counter ::ᵥ priorNum ::ᵥ av)
 let output := Term.numeral result
 let P := Formula.equal priorCall priorNum
 let seed := PrescribedRuntimeSpecialization.produce (rootFormula f tag)
  (Fin.cases (Term.numeral counter) (fun i => Term.numeral (inputs.get i)))
  (PrescribedSourceAxiomSpecialization.seed (rootFormula f tag))
 let congruence := unaryRuleNumber (closedStepFunction (tag+stepTag f) counter inputs) priorCall priorNum
 let liftedRoot := liftNumber (.equal nextCall left) P seed
 let first := transitivityUnderNumber P nextCall left right liftedRoot congruence
 let liftedChild := liftNumber (.equal right output) P childCode
 transitivityUnderNumber P nextCall right output first liftedChild

def certificate {arity k m ctx : Nat} {p : Program arity} {installed : Formula 1}
 {lhs rhs : Term 1} {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (f : Program m) (tag : Nat) (counter : Term ctx) (inputs : List.Vector (Term ctx) m)
 (previous result childCode : Term ctx) : Term ctx :=
 let J := tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag previous
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag)
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ av)
 let left := callValue J (Term.numeral (tag+stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ av)
 let right := callValue J (Term.numeral (tag+stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let P := equalValue J.ctag J.atag priorCall priorNum
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula f tag) (counterRaw ::ᵥ av)
 let congruence := unaryRuleCertificate I (stepEnvironment m) (stepTemplate m (tag+stepTag f))
  (counterRaw ::ᵥ av) priorCall priorNum
 let liftedRoot := liftCertificate I (equalValue J.ctag J.atag nextCall left) P seed
 let first := transitivityUnderCertificate I P nextCall left right liftedRoot congruence
 let liftedChild := liftCertificate I (equalValue J.ctag J.atag right output) P childCode
 transitivityUnderCertificate I P nextCall right output first liftedChild
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate
