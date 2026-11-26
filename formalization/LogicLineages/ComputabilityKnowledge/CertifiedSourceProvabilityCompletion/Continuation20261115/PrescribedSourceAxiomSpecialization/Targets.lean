module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
/-- Same already selected actual tuple and installed uniform checker. One seed
fuel precedes every original root axiom and every runtime specialization.
The literal axiom-line CORE seed is derived, never assumed. -/
def InternalSeededSpecialization : Prop :=
 ∀ (old arithmetic : Program 1) (x : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (verifier old arithmetic x) c →
 (∀ v, evaluate x v = SixSol20261113.HistoryDispatcher.axiomFunction v) →
 ∀ (I : UniformClosedRule13Certificate.Installation (root pF pR old arithmetic x)
  old arithmetic (SixSol20261113.SaturatedAxiomLeaf.saturated x)) (mtag : Nat),
 (nodes (root pF pR old arithmetic x))[mtag]? = some ⟨4,SixSol20261113.LiteralRawMP.constructor⟩ →
 ∃ seedFuel : Nat, ∀ n (f : Formula n),
 GorbowStandardInduction.universalClosure f ∈ GorbowPRDefiningEquations.axioms (root pF pR old arithmetic x) →
 ∀ ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n) (larger : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)) →
 let B := PrescribedRuntimeSpecialization.value I.ctag I.atag f raw
 let code := certificate mtag I.ctag I.atag I.constructorTag f raw
 Nonempty (Hilbert.Local (S pF pR (verifier old arithmetic x)) ctx G
  (.conj (.equal (SixSol20261113.LiteralCheckerAcceptance.coreCall I.coreTag
   (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.verifierTag (Term.numeral (Encodable.encode c)) larger .zero (.add B B) code)))
/-- Exact source proof of the same prescribed numeric trace seeded by the
original axiomLine. Equality holds even without assuming the seed is admitted;
admission is required above for acceptance, not for code arithmetic. -/
def InternalSeededTrace : Prop :=
 ∀ (old arithmetic : Program 1) (x : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (verifier old arithmetic x) c →
 ∀ (I : UniformClosedRule13Certificate.Installation (root pF pR old arithmetic x)
  old arithmetic (SixSol20261113.SaturatedAxiomLeaf.saturated x)) (mtag : Nat),
 (nodes (root pF pR old arithmetic x))[mtag]? = some ⟨4,SixSol20261113.LiteralRawMP.constructor⟩ →
 ∀ n (f : Formula n) (sigma : Fin n → Term 0) ctx,
 Nonempty (Derivation (S pF pR (verifier old arithmetic x))
  (.equal (certificate mtag I.ctag I.atag I.constructorTag f
   (PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) sigma))
   (Term.numeral (PrescribedRuntimeSpecialization.produce f sigma (seed f)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Targets
