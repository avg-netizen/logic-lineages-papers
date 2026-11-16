module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Same current source and checker. Seed fuel precedes all actual root axioms;
only actual raw-term validators and the fuel guard are caller obligations. -/
def InternalSeededSpecialization : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ n (f : Formula n),
 GorbowStandardInduction.universalClosure f ∈ GorbowPRDefiningEquations.axioms
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX) →
 ∀ ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n) (larger : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)) →
 let B := PrescribedRuntimeSpecialization.value I.previous.current.ctag I.previous.current.atag f raw
 let code := PrescribedSourceAxiomSpecialization.certificate
  I.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag
  I.previous.current.constructorTag f raw
 Nonempty (Hilbert.Local (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)) ctx G
  (.conj (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag
   (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.current.verifierTag
    (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code)))
/-- Exact original numeric recipe; no admitted seed or opaque certificate choice. -/
def InternalSeededTrace : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX) c →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ n (f : Formula n) (sigma : Fin n → Term 0) ctx,
 Nonempty (Derivation (S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX))
  (.equal (PrescribedSourceAxiomSpecialization.certificate
   I.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag
   I.previous.current.constructorTag f (PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma))
   (Term.numeral (PrescribedRuntimeSpecialization.produce f sigma
    (PrescribedSourceAxiomSpecialization.seed f)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Targets
