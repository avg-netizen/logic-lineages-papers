module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericExistentialSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericTransportProof
open GorbowSyntax GorbowTheoryProof GorbowPRDefiningEquations
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph
open PrescribedRuntimeEquality HistoryCodec.ArithmeticSupport
/-- Use the verifier half only, with genuine equality of its calls and the
closed sorted/raw alignment lifted to this context. -/
theorem acceptedToProv {ctx : Nat} (U : Sentence → Prop)
 (namedTag index coreTag verifierTag : Nat) (fuel raw code u : Term ctx)
 (halign : Nonempty (Derivation U (.equal
  u (.add raw raw))))
 (hcoh : Nonempty (Derivation U (.equal
  (call verifierTag (inputs (Term.numeral index) fuel .zero (.add raw raw) code))
  (call namedTag
   (inputs (Term.numeral index) fuel .zero (.add raw raw) code))))) :
 Nonempty (Derivation U (.imp
  (accepted coreTag verifierTag (Term.numeral index) fuel raw code)
  (GenericExistentialSyntax.prov namedTag index u))) := by
 obtain ⟨ha⟩ := halign
 obtain ⟨hc⟩ := hcoh
 let P := accepted coreTag verifierTag (Term.numeral (n := ctx) index) fuel raw code
 let G := [P]
 have hp : Hilbert.Local U ctx G P := .hypothesis List.mem_cons_self
 have hs := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hp
 have hn := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hc)) hs
 have he : Hilbert.Local U ctx G (.equal
  (call namedTag
   (inputs (Term.numeral index) fuel .zero
    u code))
  (call namedTag
   (inputs (Term.numeral index) fuel .zero (.add raw raw) code))) := by
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
 obtain ⟨hi⟩ := GenericExistentialSyntax.introduce U namedTag
  index fuel u code
 exact ⟨(Hilbert.Local.mp (.base hi) hsuccess).discharge.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericTransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericTransportProof
