module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
/-- Exact literal numeric trace, including unrestricted malformed child codes.
This is a constructor helper, not full producer correctness. -/
def InternalTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ m n (f : Program n) (g : Fin n → Program m) tag
 (inputs : List.Vector Nat m) (values : List.Vector Nat n) result
 (codes : List.Vector Nat n) functionCode ctx,
 Nonempty (Derivation (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX))
  (.equal (certificate I f g tag (inputs.map (Term.numeral (n := ctx)))
   (values.map Term.numeral) (Term.numeral result) (codes.map Term.numeral) (Term.numeral functionCode))
   (Term.numeral (number f g tag inputs values result codes functionCode))))
/-- Actual installed composition constructor at the same current source, with
one fuel bound before all node choices and runtime inputs. Only child/function
calculation CORE premises remain: they are to be discharged by AST induction.
The root axiom seed, all numeral validity, and encoding coherence are internal. -/
def InternalConstructor : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m n (f : Program n) (g : Fin n → Program m) tag,
 (nodes (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨m,Program.composition f g⟩ →
 ∀ ctx (G : List (Formula ctx)) (inputs : List.Vector (Term ctx) m)
 (values codes : List.Vector (Term ctx) n) (result functionCode fuel : Term ctx),
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 (∀ i, Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (core I.current.coreTag index fuel (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (core I.current.coreTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral (tag+1)) cv)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result)) functionCode)) →
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral tag) av)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (certificate I f g tag inputs values result codes functionCode)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.Targets
