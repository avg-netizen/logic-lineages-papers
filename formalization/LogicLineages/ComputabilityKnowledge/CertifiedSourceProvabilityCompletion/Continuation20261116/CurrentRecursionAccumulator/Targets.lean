module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality

/-- All raw outputs, all counts; no acceptance/calibration premise. -/
def NativeRawTrace : Prop := ∀ m (base : Program m) (formula step : Program (m+1))
 (params : List.Vector Nat m) counter,
 evaluate (producer base formula step) (counter ::ᵥ params) =
 rawNumber (fun n => evaluate formula (n ::ᵥ params))
  (fun n => evaluate step (n ::ᵥ params)) (evaluate base params) counter
/-- Exact original recurrence once the formula program quotes the original
family. This premise is only prefix-code calibration, never acceptance. Base
and step outputs remain arbitrary numeric codes. -/
def NativeOriginalTrace : Prop := ∀ m (base : Program m) (formula step : Program (m+1))
 (params : List.Vector Nat m) (phi : Nat → Formula 0),
 (∀ n, evaluate formula (n ::ᵥ params) = Encodable.encode (GorbowFormulaPrefixCode.encode (phi n))) →
 ∀ counter, evaluate (producer base formula step) (counter ::ᵥ params) =
 number phi (fun n => evaluate step (n ::ᵥ params)) (evaluate base params) counter
/-- Runtime graph of the exact installed recursion AST, not a supplied graph
oracle. One actual original MP joins the step and prior producer accumulator. -/
def InternalEquations : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m (base : Program m) (formula step : Program (m+1)),
 ∀ R : Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) base formula step,
 ∀ ctx (counter : Term ctx) (params : List.Vector (Term ctx) m),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 Nonempty (Derivation U
  (.conj
   (.equal (familyCall R.producerTag .zero params) (call R.baseTag params))
   (.equal (familyCall R.producerTag (.succ counter) params)
    (LiteralMPRun.certificate I.previous.previous.previous.previous.previous.mpTag .zero
     (familyCall R.formulaTag (.succ counter) params)
     (familyCall R.stepTag counter params) (familyCall R.producerTag counter params)))))
/-- Literal installed call equals raw decoded recurrence at every numeral,
including malformed base, step and formula outputs. -/
def InternalNumeralTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m (base : Program m) (formula step : Program (m+1)),
 ∀ R : Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) base formula step,
 ∀ ctx counter (params : List.Vector Nat m),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.equal (familyCall R.producerTag (Term.numeral counter) (params.map (Term.numeral (n := ctx))))
   (Term.numeral (rawNumber (fun n => evaluate formula (n ::ᵥ params))
    (fun n => evaluate step (n ::ᵥ params)) (evaluate base params) counter))))
/-- Genuine object-language induction at the SAME fixed source/index/fuel.
Base and ordinary step-implication CORE proofs are premises. There is no
previous-CORE premise: only the induction hypothesis supplies acceptance of
the actual recursive producer accumulator. No generic phi success oracle.
This is conditional closure, not a completed installation or AST producer. -/
def InternalAccumulator : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m (base : Program m) (formula step : Program (m+1)),
 ∀ R : Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) base formula step,
 ∀ ctx (params : List.Vector (Term ctx) m) (index fuel counter : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Derivation U
  (core I.currentK.coreTag index fuel (familyCall R.formulaTag .zero params) (call R.baseTag params))) →
 Nonempty (Derivation U
  (core I.currentK.coreTag (SixSol20261112.Fuel.liftTerm index) (SixSol20261112.Fuel.liftTerm fuel)
   (impValue J.ctag J.atag
    (familyCall R.formulaTag (.var 0 : Term (ctx+1)) (params.map SixSol20261112.Fuel.liftTerm))
    (familyCall R.formulaTag (.succ (.var 0)) (params.map SixSol20261112.Fuel.liftTerm)))
   (familyCall R.stepTag (.var 0) (params.map SixSol20261112.Fuel.liftTerm)))) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (familyCall R.formulaTag counter params) (familyCall R.producerTag counter params)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Targets
