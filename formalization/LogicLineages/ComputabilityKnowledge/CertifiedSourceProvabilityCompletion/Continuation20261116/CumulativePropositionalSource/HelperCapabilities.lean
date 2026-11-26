module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
/-- Reinstalled CurrentSourceAxiomSeed.InternalCurrentSeed at this actual new source/root. -/
def SeedCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∃ seedFuel : Nat, ∀ sigma : Sentence,
 sigma ∈ GorbowPRDefiningEquations.axioms
  (root installed lhs rhs pF pR old a baseX) →
 ∀ ctx (larger : Term ctx),
 Nonempty (Derivation (S pF pR (verifier installed lhs rhs old a baseX))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)
   (.conj
    (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag
     (Term.numeral (Encodable.encode c)) larger .zero
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
     (Term.numeral (FiniteRuleFourCertificate.certificateCode sigma))) (.succ .zero))
    (SixSol20261112.Fuel.success I.currentK.verifierTag
     (Term.numeral (Encodable.encode c)) larger .zero
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
     (Term.numeral (FiniteRuleFourCertificate.certificateCode sigma))))))
/-- Reinstalled CurrentSourceSeededSpecialization.InternalSeededSpecialization at this actual new source/root. -/
def SpecializationCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∃ seedFuel : Nat, ∀ n (f : Formula n),
 GorbowStandardInduction.universalClosure f ∈ GorbowPRDefiningEquations.axioms
  (root installed lhs rhs pF pR old a baseX) →
 ∀ ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n) (larger : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)) →
 let B := PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag f raw
 let code := PrescribedSourceAxiomSpecialization.certificate
  I.previous.previous.previous.previous.previous.mpTag I.previous.previous.current.ctag I.previous.previous.current.atag
  I.previous.previous.current.constructorTag f raw
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (.conj (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag
   (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.currentK.verifierTag
    (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code)))
/-- Reinstalled CurrentSourceSeededSpecialization.InternalSeededTrace at this actual new source/root. -/
def SpecializationTraceCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ n (f : Formula n) (sigma : Fin n → Term 0) ctx,
 Nonempty (Derivation (S pF pR (verifier installed lhs rhs old a baseX))
  (.equal (PrescribedSourceAxiomSpecialization.certificate
   I.previous.previous.previous.previous.previous.mpTag I.previous.previous.current.ctag I.previous.previous.current.atag
   I.previous.previous.current.constructorTag f (PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma))
   (Term.numeral (PrescribedRuntimeSpecialization.produce f sigma
    (PrescribedSourceAxiomSpecialization.seed f)))))
/-- Reinstalled CurrentCompositionCertificate.InternalTrace at this actual new source/root. -/
def CompositionTraceCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ m n (f : Program n) (g : Fin n → Program m) tag
 (inputs : List.Vector Nat m) (values : List.Vector Nat n) result
 (codes : List.Vector Nat n) functionCode ctx,
 Nonempty (Derivation (S pF pR (verifier installed lhs rhs old a baseX))
  (.equal (CurrentCompositionCertificate.certificate I.previous f g tag (inputs.map (Term.numeral (n := ctx)))
   (values.map Term.numeral) (Term.numeral result) (codes.map Term.numeral) (Term.numeral functionCode))
   (Term.numeral (CurrentCompositionCertificate.number f g tag inputs values result codes functionCode))))
/-- Reinstalled CurrentCompositionCertificate.InternalConstructor at this actual new source/root. -/
def CompositionCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∃ seedFuel : Nat, ∀ m n (f : Program n) (g : Fin n → Program m) tag,
 (nodes (root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨m,Program.composition f g⟩ →
 ∀ ctx (G : List (Formula ctx)) (inputs : List.Vector (Term ctx) m)
 (values codes : List.Vector (Term ctx) n) (result functionCode fuel : Term ctx),
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let bv := CurrentCompositionCertificate.childValues J f g tag av
 let cv := CurrentCompositionCertificate.numeralValues J.numeralTag values
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 (∀ i, Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral (tag+1)) cv)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result)) functionCode)) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral tag) av)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (CurrentCompositionCertificate.certificate I.previous f g tag inputs values result codes functionCode)))
/-- Reinstalled CurrentRecursionBaseCertificate.InternalTrace at this actual new source/root. -/
def RecursionBaseTraceCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ m tag (inputs : List.Vector Nat m) result childCode ctx,
 Nonempty (Derivation (S pF pR (verifier installed lhs rhs old a baseX))
  (.equal (CurrentRecursionBaseCertificate.certificate I.previous tag (inputs.map (Term.numeral (n := ctx)))
    (Term.numeral result) (Term.numeral childCode))
   (Term.numeral (CurrentRecursionBaseCertificate.number tag inputs result childCode))))
/-- Reinstalled CurrentRecursionBaseCertificate.InternalConstructor at this actual new source/root. -/
def RecursionBaseCapability {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∃ seedFuel : Nat, ∀ m (f : Program m) (g : Program (m+2)) tag,
 (nodes (root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨m+1,Program.recursion f g⟩ →
 ∀ ctx (G : List (Formula ctx)) (inputs : List.Vector (Term ctx) m)
 (result childCode fuel : Term ctx),
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let av := CurrentRecursionBaseCertificate.numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral (tag+1)) av)
    (LiteralNumeralPrefix.numeralCall J.numeralTag result)) childCode)) →
 Nonempty (Hilbert.Local (S pF pR (verifier installed lhs rhs old a baseX)) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue J.ctag J.atag (callValue J (Term.numeral tag) (zero ::ᵥ av))
    (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (CurrentRecursionBaseCertificate.certificate I.previous tag inputs result childCode)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource
