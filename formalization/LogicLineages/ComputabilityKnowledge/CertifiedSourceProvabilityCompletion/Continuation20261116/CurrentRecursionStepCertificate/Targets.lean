module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence CurrentImplicationCertificate CurrentEqualityImplication

/-- General-environment literal trace bridge needed by the step template.
Only encoding equalities are inputs; no acceptance premise or logical oracle.
The resulting number is the same original unaryCongruenceRule recipe. -/
def GeneralUnaryTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (template : Term n)
 ctx (raw : List.Vector (Term ctx) inputs) (aF bF : Term ctx) (f : Term 1) (left right : Term 0),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 Nonempty (Derivation U (.equal aF (rawNumeral left))) →
 Nonempty (Derivation U (.equal bF (rawNumeral right))) →
 Nonempty (Derivation U (.equal (FixedFormulaSubstitution.termValue J.ctag J.atag e raw template)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f))))) →
 Nonempty (Derivation U (.equal (specializedValue J.ctag J.atag e template raw aF)
  (rawNumeral (GorbowClosedEquality.instantiateTerm f left)))) →
 Nonempty (Derivation U (.equal (specializedValue J.ctag J.atag e template raw bF)
  (rawNumeral (GorbowClosedEquality.instantiateTerm f right)))) →
 Nonempty (Derivation U (.equal (unaryRuleCertificate I e template raw aF bF)
  (Term.numeral (unaryRuleNumber f left right))))
/-- Literal original ordered successor implication numeric recipe, arbitrary
step-child code numbers including malformed decode/default behavior. -/
def InternalTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m (f : Program m) tag counter (inputs : List.Vector Nat m) previous result childCode ctx,
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.equal (certificate I f tag (Term.numeral counter) (inputs.map (Term.numeral (n := ctx)))
   (Term.numeral previous) (Term.numeral result) (Term.numeral childCode))
   (Term.numeral (number f tag counter inputs previous result childCode))))
/-- Actual source successor implication: fixed root seed fuel before node/runtime
choices; only actual node membership, original fuel guard and the step-child's
calculation CORE are inputs. No previous CORE premise while synthesizing
this implication. Previous/result values are arbitrary; matching semantics can
later specialize them, and cannot replace the step-child CORE premise. -/
def InternalConstructor : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m (f : Program m) (g : Program (m+2)) tag,
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨m+1,Program.recursion f g⟩ →
 ∀ ctx (G : List (Formula ctx)) (counter : Term ctx) (inputs : List.Vector (Term ctx) m)
 (previous result childCode fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag previous
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag)
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ av)
 let child := callValue J (Term.numeral (tag+stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local U ctx G (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local U ctx G (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag child output) childCode)) →
 Nonempty (Hilbert.Local U ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (impValue J.ctag J.atag (equalValue J.ctag J.atag priorCall priorNum) (equalValue J.ctag J.atag nextCall output))
  (certificate I f tag counter inputs previous result childCode)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.Targets
