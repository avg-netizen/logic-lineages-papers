module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- All new syntax is fixed before the once-only source/tag selection. -/
def producerItems {m : Nat} (base : Program m) (step : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) : List Packed :=
 [⟨m+1,.recursion base step⟩,⟨m,base⟩,⟨m+2,step⟩,⟨m+1,B⟩,⟨m+3,G⟩,
  ⟨m+2,CurrentCalculationFormulaProgram.program (.recursion base step)⟩,
  ⟨m+1,CurrentRecursionBaseProgram.program base B⟩,
  ⟨m+2,CurrentRecursionStepProgram.program base step G⟩,
  ⟨m+2,CurrentRecursionProducerProgram.formula base step⟩,
  ⟨m+2,CurrentRecursionProducerProgram.step base step G⟩,
  ⟨m+3,CurrentRecursionAccumulator.join (CurrentRecursionProducerProgram.formula base step)
    (CurrentRecursionProducerProgram.step base step G)⟩,
  ⟨m+2,CurrentRecursionProducerProgram.accumulator base step B G⟩,
  ⟨m+2,CurrentRecursionProducerProgram.program base step B G⟩]
def producerCarrier {m : Nat} (base : Program m) (step : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) : Program 6 :=
 ReflexivityInstalled.bundle (producerItems base step B G)
/-- Embed the entire old extra unchanged, not an old selected source tuple. -/
def extendedExtra {k m : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩,
   ⟨6,producerCarrier base step B G⟩]
/-- Actual existential outputs of source selection. No field is a success oracle.
Both evaluator child addresses come from ONE q occurrence. -/
structure Installation {arity k m : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3)) where
 extraTag : Nat
 oldExtraTag : Nat
 carrierTag : Nat
 qTag : Nat
 BTag : Nat
 GTag : Nat
 BJ : CurrentRecursionBaseProgram.Tags
 SJ : CurrentRecursionStepProgram.Tags
 producer : CurrentRecursionProducerProgram.GraphNodes p base step B G
 hExtra : (nodes p)[extraTag]? = some ⟨6,extendedExtra installed lhs rhs t old a baseX base step B G⟩
 hOldExtra : (nodes p)[oldExtraTag]? = some ⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩
 hCarrier : (nodes p)[carrierTag]? = some ⟨6,producerCarrier base step B G⟩
 hItems : ∀ q ∈ producerItems base step B G, ∃ (tag : Nat), (nodes p)[tag]? = some q
 hQ : (nodes p)[qTag]? = some ⟨m+1,.recursion base step⟩
 hBase : (nodes p)[qTag+1]? = some ⟨m,base⟩
 hStep : (nodes p)[qTag+GorbowPRChildTags.stepTag base]? = some ⟨m+2,step⟩
 hB : (nodes p)[BTag]? = some ⟨m+1,B⟩
 hG : (nodes p)[GTag]? = some ⟨m+3,G⟩
 baseInstallation : CurrentRecursionBaseProgram.Installation p base B BJ
 stepInstallation : CurrentRecursionStepProgram.Installation p base step G SJ
 baseAddress : BJ.baseTag = qTag+1
 baseChildAddress : BJ.childTag = BTag
 recursionAddress : SJ.qtag = qTag
 stepAddress : SJ.stepTag = qTag+GorbowPRChildTags.stepTag base
 stepChildAddress : SJ.childTag = GTag
 mpAddress : producer.mpTag = SJ.mtag
/-- All equations live in the SAME selected source. Target is arbitrary syntax;
instantiate it with numeral(qTag) for actual recursion correctness later. -/
def SourceEquations {k m : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a baseX base step B G) : Prop :=
 ∀ ctx (target counter : Term ctx) (inputs : List.Vector (Term ctx) m),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := CurrentCalculationFormulaProgram.codecTags R.SJ.ctag R.SJ.atag R.SJ.ntag
 Nonempty (Derivation U (.equal (call R.producer.formulaTag (target ::ᵥ counter ::ᵥ inputs))
  (equalValue R.SJ.ctag R.SJ.atag
   (callValue K target ((counter ::ᵥ inputs).map (LiteralNumeralPrefix.numeralCall R.SJ.ntag)))
   (LiteralNumeralPrefix.numeralCall R.SJ.ntag (call R.qTag (counter ::ᵥ inputs)))))) ∧
 Nonempty (Derivation U (.equal (call R.producer.baseTag (target ::ᵥ inputs))
  (CurrentRecursionBaseProgram.value R.BJ target inputs))) ∧
 Nonempty (Derivation U (.equal (call R.producer.stepTag (target ::ᵥ counter ::ᵥ inputs))
  (CurrentRecursionStepProgram.value base R.SJ target counter inputs))) ∧
 Nonempty (Derivation U (.conj
  (.equal (call R.producer.publicTag (target ::ᵥ .zero ::ᵥ inputs)) (call R.producer.baseTag (target ::ᵥ inputs)))
  (.equal (call R.producer.publicTag (target ::ᵥ .succ counter ::ᵥ inputs))
   (LiteralMPRun.certificate R.producer.mpTag .zero
    (call R.producer.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs))
    (call R.producer.stepTag (target ::ᵥ counter ::ᵥ inputs))
    (call R.producer.publicTag (target ::ᵥ counter ::ᵥ inputs)))))) ∧
 Nonempty (Derivation U (.equal (call R.qTag (.zero ::ᵥ inputs)) (call (R.qTag+1) inputs))) ∧
 Nonempty (Derivation U (.equal (call R.qTag (.succ counter ::ᵥ inputs))
  (call (R.qTag+GorbowPRChildTags.stepTag base) (counter ::ᵥ call R.qTag (counter ::ᵥ inputs) ::ᵥ inputs))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource
