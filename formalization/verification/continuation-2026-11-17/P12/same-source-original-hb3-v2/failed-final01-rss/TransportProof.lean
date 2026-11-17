module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ExistentialSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.CoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.TransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open SixSol20261112.Fuel NamedArithmeticGraph
open GorbowSubstitution GorbowFormulaSubstitution
open PrescribedRuntimeEquality HistoryCodec.ArithmeticSupport
/-- Use the verifier half only, with genuine equality of its calls and the
closed sorted/raw alignment lifted to this context. -/
theorem acceptedToProv {ctx : Nat} (U : Sentence → Prop) (pF : Program 1) (c : Code)
 (sigma : Sentence) (coreTag verifierTag : Nat) (fuel raw code : Term ctx)
 (halign : Nonempty (Derivation U (.equal
  (LiteralCheckerSuccessBridge.value pF c (prD pF c sigma)) (.add raw raw))))
 (hcoh : Nonempty (Derivation U (.equal
  (call verifierTag (inputs (Term.numeral (Encodable.encode c)) fuel .zero (.add raw raw) code))
  (call (GorbowNamedInternalProvability.checkerTag pF)
   (inputs (Term.numeral (Encodable.encode c)) fuel .zero (.add raw raw) code))))) :
 Nonempty (Derivation U (.imp
  (accepted coreTag verifierTag (Term.numeral (Encodable.encode c)) fuel raw code)
  (applyProv pF c (LiteralCheckerSuccessBridge.value pF c (prD pF c sigma))))) := by
 obtain ⟨ha⟩ := halign
 obtain ⟨hc⟩ := hcoh
 let P := accepted coreTag verifierTag (Term.numeral (n := ctx) (Encodable.encode c)) fuel raw code
 let G := [P]
 have hp : Hilbert.Local U ctx G P := .hypothesis List.mem_cons_self
 have hs := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hp
 have hn := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hc)) hs
 have he : Hilbert.Local U ctx G (.equal
  (call (GorbowNamedInternalProvability.checkerTag pF)
   (inputs (Term.numeral (Encodable.encode c)) fuel .zero
    (LiteralCheckerSuccessBridge.value pF c (prD pF c sigma)) code))
  (call (GorbowNamedInternalProvability.checkerTag pF)
   (inputs (Term.numeral (Encodable.encode c)) fuel .zero (.add raw raw) code))) := by
  apply LiteralRawMP.DispatcherSupportProof.callCongruence
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact .base (.logical (.reflexive _))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact .base (.logical (.reflexive _))
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact .base (.logical (.reflexive _))
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact .base ha
        · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
          exact .base (.logical (.reflexive _))
 have hsuccess := localTrans _ _ _ he hn
 obtain ⟨hi⟩ := ExistentialSyntax.introduce U (GorbowNamedInternalProvability.checkerTag pF)
  (Encodable.encode c) fuel (LiteralCheckerSuccessBridge.value pF c (prD pF c sigma)) code
 rw [ExistentialSyntax.original] at hi
 exact ⟨(Hilbert.Local.mp (.base hi) hsuccess).discharge.finish⟩

theorem liftAlignment (U : Sentence → Prop) (pF : Program 1) (c : Code) (sigma : Sentence)
 (h : Nonempty (Derivation U (.equal
  (LiteralCheckerSuccessBridge.value (ctx := 0) pF c (prD pF c sigma))
  (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))))))
 (ctx : Nat) : Nonempty (Derivation U (.equal
  (LiteralCheckerSuccessBridge.value (ctx := ctx) pF c (prD pF c sigma))
  (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))))) := by
 obtain ⟨hh⟩ := GorbowDerivationSubstitution.Proof.derivationSubstitution U 0 ctx _ Fin.elim0 h
 simpa only [substituteFormula,substitute,Logic.substNumeral,
  LiteralCheckerSuccessBridge.LiteralNaturality.valueSubst] using (show Nonempty _ from ⟨hh⟩)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.TransportProof
