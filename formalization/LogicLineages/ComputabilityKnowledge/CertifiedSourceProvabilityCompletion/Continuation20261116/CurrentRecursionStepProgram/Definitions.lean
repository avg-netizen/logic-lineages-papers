module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Fixed syntactic offset: successor iteration, not quoted addition syntax. -/
def shiftTerm {ctx : Nat} (offset : Nat) (t : Term ctx) : Term ctx := Nat.rec t (fun _ v => .succ v) offset
def shiftProgram {arity : Nat} (offset : Nat) (q : Program arity) : Program arity := Nat.rec q (fun _ v => applyOne .succ v) offset
def params (m : Nat) : List.Vector (Term (m+2)) m :=
 List.Vector.ofFn (fun i => .var i.succ.castSucc)
def priorTemplate (m : Nat) : Term (m+2) :=
 CurrentRecursionBaseProgram.openCall (.var (Fin.last (m+1))) (.var 0 ::ᵥ params m)
def nextTemplate (m : Nat) : Term (m+2) :=
 CurrentRecursionBaseProgram.openCall (.var (Fin.last (m+1))) (.succ (.var 0) ::ᵥ params m)
def leftTemplate (m offset : Nat) : Term (m+2) :=
 CurrentRecursionBaseProgram.openCall (shiftTerm offset (.var (Fin.last (m+1))))
  (.var 0 ::ᵥ priorTemplate m ::ᵥ params m)
/-- m+1 original input binders; last free coordinate is runtime target tag. -/
def rootTemplate (m offset : Nat) : Formula (m+2) := .equal (nextTemplate m) (leftTemplate m offset)
def rightTemplate (m offset : Nat) : Term (m+3) :=
 CurrentRecursionBaseProgram.openCall (shiftTerm offset (.var (Fin.last (m+2))))
  (.var 0 ::ᵥ .var 1 ::ᵥ List.Vector.ofFn (fun i : Fin m => .var i.succ.succ.castSucc))
/-- Protected accumulator is coordinate0; closed coordinates are counter,
original inputs, and runtime target tag. -/
def unaryTemplate (m offset : Nat) : Term (m+3) :=
 CurrentRecursionBaseProgram.openCall (shiftTerm offset (.var (Fin.last (m+2))))
  (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.ofFn (fun i : Fin m => .var i.succ.succ.castSucc))
def termQuote {n arity : Nat} (t : Term n) (raw : Fin n → Program arity) : Program arity :=
 .composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.runtimeEnvironment n) t) raw
/-- Runtime input order: target, counter, original numeric inputs. -/
def previous {m : Nat} (base : Program m) (step : Program (m+2)) : Program (m+2) :=
 CurrentCalculationFormulaProgram.tailProgram (.recursion base step)
def stepArguments {m : Nat} (base : Program m) (step : Program (m+2)) : Fin (m+2) → Program (m+2) :=
 Fin.cases (.projection 1) (Fin.cases (previous base step) (fun i => .projection i.succ.succ))
def result {m : Nat} (base : Program m) (step : Program (m+2)) : Program (m+2) := .composition step (stepArguments base step)
def childArguments {m : Nat} (base : Program m) (step : Program (m+2)) : Fin (m+3) → Program (m+2) :=
 Fin.cases (shiftProgram (stepTag base) (.projection 0)) (stepArguments base step)
def rightArguments {m : Nat} (base : Program m) (step : Program (m+2)) : Fin (m+3) → Program (m+2) :=
 Fin.lastCases (applyOne LiteralNumeralPrefix.numeralCode (.projection 0))
  (Fin.cases (applyOne LiteralNumeralPrefix.numeralCode (.projection 1))
   (Fin.cases (applyOne LiteralNumeralPrefix.numeralCode (previous base step))
    (fun i => applyOne LiteralNumeralPrefix.numeralCode (.projection i.succ.succ))))
def unaryCode (m offset : Nat) : Program (m+2) :=
 .composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.headEnvironment (m+2)) (unaryTemplate m offset))
  (CurrentRecursionBaseProgram.rootArguments (m+1))

def propositional {arity : Nat} (isS : Bool) (a b c : Program arity) : Program arity :=
 CurrentRecursionBaseProgram.singleton (.composition (UniformClosedPropositional.lineConstructor isS)
  (Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))))
def liftProgram {arity : Nat} (A B code : Program arity) : Program arity :=
 CurrentRecursionBaseProgram.mp (FixedFormulaSubstitution.binary 7 B A) (propositional false A B A) code
def mpUnderProgram {arity : Nat} (P Q R hi ha : Program arity) : Program arity :=
 let imp : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 7
 CurrentRecursionBaseProgram.mp (imp P R)
  (CurrentRecursionBaseProgram.mp (imp (imp P Q) (imp P R)) (propositional true P Q R) hi) ha
def reflexivity {arity : Nat} (raw : Program arity) : Program arity :=
 CurrentRecursionBaseProgram.singleton (applyOne RawReflexivity.lineConstructor raw)
def unaryRule {arity : Nat} (openCode t u ft fu : Program arity) : Program arity :=
 let eq : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 0
 let P := eq t u
 let Q := eq ft ft
 let R := eq ft fu
 mpUnderProgram P Q R (CurrentRecursionBaseProgram.replacement (eq ft openCode) t u)
  (liftProgram Q P (reflexivity ft))
def transitivityUnder {arity : Nat} (P left middle right hleft hright : Program arity) : Program arity :=
 let eq : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 0
 let imp : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 7
 let TU := eq left middle
 let UV := eq middle right
 let TV := eq left right
 let matrix := CurrentRecursionBaseProgram.headQuote (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left)
 let seed := CurrentRecursionBaseProgram.replacement matrix middle right
 let first := mpUnderProgram P UV (imp TU TV) (liftProgram (imp UV (imp TU TV)) P seed) hright
 mpUnderProgram P TU TV first hleft
/-- Exactly the original successor recipe. No prior certificate is an input. -/
def program {m : Nat} (base : Program m) (step : Program (m+2)) (child : Program (m+3)) : Program (m+2) :=
 let raws := CurrentRecursionBaseProgram.rootArguments (m+1)
 let priorCall := termQuote (priorTemplate m) raws
 let priorNum := applyOne LiteralNumeralPrefix.numeralCode (previous base step)
 let nextCall := termQuote (nextTemplate m) raws
 let left := termQuote (leftTemplate m (stepTag base)) raws
 let right := termQuote (rightTemplate m (stepTag base)) (rightArguments base step)
 let output := applyOne LiteralNumeralPrefix.numeralCode (result base step)
 let P := FixedFormulaSubstitution.binary 0 priorCall priorNum
 let seed := CurrentRecursionBaseProgram.seedProgram (m+1) (rootTemplate m (stepTag base)) raws
 let congruence := unaryRule (unaryCode m (stepTag base)) priorCall priorNum left right
 let liftedRoot := liftProgram (FixedFormulaSubstitution.binary 0 nextCall left) P seed
 let first := transitivityUnder P nextCall left right liftedRoot congruence
 let liftedChild := liftProgram (FixedFormulaSubstitution.binary 0 right output) P (.composition child (childArguments base step))
 transitivityUnder P nextCall right output first liftedChild

structure Tags where
 ptag : Nat
 ctag : Nat
 atag : Nat
 ntag : Nat
 mtag : Nat
 r12 : Nat
 r13 : Nat
 ktag : Nat
 stag : Nat
 reflexivityTag : Nat
 qtag : Nat
 stepTag : Nat
 childTag : Nat
def baseTags (J : Tags) : CurrentRecursionBaseProgram.Tags :=
 ⟨J.ptag,J.ctag,J.atag,J.ntag,J.mtag,J.r12,J.r13,J.qtag,J.childTag⟩
structure Installation {arity m : Nat} (p : Program arity) (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : Tags) : Prop where
 hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩
 h12 : (nodes p)[J.r12]? = some ⟨3,UniformClosedRule12.lineConstructor⟩
 h13 : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩
 hk : (nodes p)[J.ktag]? = some ⟨3,UniformClosedPropositional.lineConstructor false⟩
 hs : (nodes p)[J.stag]? = some ⟨3,UniformClosedPropositional.lineConstructor true⟩
 hr : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩
 hq : (nodes p)[J.qtag]? = some ⟨m+1,Program.recursion base step⟩
 hstep : (nodes p)[J.stepTag]? = some ⟨m+2,step⟩
 hchild : (nodes p)[J.childTag]? = some ⟨m+3,child⟩

def liftValue {ctx : Nat} (J : Tags) (A B code : Term ctx) : Term ctx :=
 LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag B A)
  (UniformClosedPropositionalCertificate.certificate J.ctag J.ktag A B A) code
def mpUnderValue {ctx : Nat} (J : Tags) (P Q R hi ha : Term ctx) : Term ctx :=
 LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag P R)
  (LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R))
   (UniformClosedPropositionalCertificate.certificate J.ctag J.stag P Q R) hi) ha
def unaryValue {ctx : Nat} (J : Tags) (openCode t u ft fu : Term ctx) : Term ctx :=
 let P := equalValue J.ctag J.atag t u
 let Q := equalValue J.ctag J.atag ft ft
 let R := equalValue J.ctag J.atag ft fu
 mpUnderValue J P Q R (UniformClosedRule12Certificate.certificate J.ctag J.r12 (equalValue J.ctag J.atag ft openCode) t u)
  (liftValue J Q P (RawCumulativeLogical.certificate J.ctag J.reflexivityTag ft))
def transitivityValue {ctx : Nat} (J : Tags) (P left middle right hleft hright : Term ctx) : Term ctx :=
 let TU := equalValue J.ctag J.atag left middle
 let UV := equalValue J.ctag J.atag middle right
 let TV := equalValue J.ctag J.atag left right
 let matrix := equalValue J.ctag J.atag left (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let seed := UniformClosedRule12Certificate.certificate J.ctag J.r12 matrix middle right
 let first := mpUnderValue J P UV (impValue J.ctag J.atag TU TV) (liftValue J (impValue J.ctag J.atag UV (impValue J.ctag J.atag TU TV)) P seed) hright
 mpUnderValue J P TU TV first hleft
/-- Arbitrary-symbolic graph exposes actual q, g and child-producer calls. -/
def value {m ctx : Nat} (base : Program m) (J : Tags) (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) : Term ctx :=
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 let cn := LiteralNumeralPrefix.numeralCall J.ntag counter
 let previous := call J.qtag (counter ::ᵥ inputs)
 let result := call J.stepTag (counter ::ᵥ previous ::ᵥ inputs)
 let child := call J.childTag (shiftTerm (GorbowPRChildTags.stepTag base) target ::ᵥ counter ::ᵥ previous ::ᵥ inputs)
 let priorCall := callValue K target (cn ::ᵥ nums)
 let priorNum := LiteralNumeralPrefix.numeralCall J.ntag previous
 let nextCall := callValue K target (LiteralNumeralPrefix.numeralCall J.ntag (.succ counter) ::ᵥ nums)
 let left := callValue K (shiftTerm (GorbowPRChildTags.stepTag base) target) (cn ::ᵥ priorCall ::ᵥ nums)
 let right := callValue K (shiftTerm (GorbowPRChildTags.stepTag base) target) (cn ::ᵥ priorNum ::ᵥ nums)
 let output := LiteralNumeralPrefix.numeralCall J.ntag result
 let raws := CurrentRecursionBaseProgram.rawValues (baseTags J) target (counter ::ᵥ inputs)
 let openCode := FixedFormulaSubstitution.termValue J.ctag J.atag (PrescribedRuntimeSpecialization.headEnvironment (m+2)) raws
  (unaryTemplate m (GorbowPRChildTags.stepTag base))
 let P := equalValue J.ctag J.atag priorCall priorNum
 let seed := CurrentRecursionBaseProgram.seedValue (baseTags J) (m+1) (rootTemplate m (GorbowPRChildTags.stepTag base)) raws
 let congruence := unaryValue J openCode priorCall priorNum left right
 let liftedRoot := liftValue J (equalValue J.ctag J.atag nextCall left) P seed
 let first := transitivityValue J P nextCall left right liftedRoot congruence
 let liftedChild := liftValue J (equalValue J.ctag J.atag right output) P child
 transitivityValue J P nextCall right output first liftedChild
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram
