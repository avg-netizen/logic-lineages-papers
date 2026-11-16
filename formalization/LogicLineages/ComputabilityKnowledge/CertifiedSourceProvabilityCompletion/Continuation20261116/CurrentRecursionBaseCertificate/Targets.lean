module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
/-- Literal numeric trace for arbitrary base-child codes, including malformed codes. -/
def InternalTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m tag (inputs : List.Vector Nat m) result childCode ctx,
 Nonempty (Derivation (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX))
  (.equal (certificate I tag (inputs.map (Term.numeral (n := ctx)))
    (Term.numeral result) (Term.numeral childCode))
   (Term.numeral (number tag inputs result childCode))))
/-- Constructor-only recursion zero case. Actual node membership, fixed seed
fuel before node/runtime choices, and only the base child's calculation CORE
premise. No recursion induction or opaque producer witness is asserted. -/
def InternalConstructor : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m (f : Program m) (g : Program (m+2)) tag,
 (nodes (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨m+1,Program.recursion f g⟩ →
 ∀ ctx (G : List (Formula ctx)) (inputs : List.Vector (Term ctx) m)
 (result childCode fuel : Term ctx),
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (core I.current.coreTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral (tag+1)) av)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result)) childCode)) →
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral tag) (zero ::ᵥ av))
    (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (certificate I tag inputs result childCode)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.Targets
