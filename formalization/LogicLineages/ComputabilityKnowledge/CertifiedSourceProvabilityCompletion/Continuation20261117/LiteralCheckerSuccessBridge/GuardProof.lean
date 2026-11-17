module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FuelWitness.ExtractionLogicProof GorbowFormulaSubstitution GorbowSubstitution
/-- Equality transport of the fuel coordinate in both actual checker calls. -/
theorem fuelTransport {ctx : Nat} (U : Sentence → Prop) (G : List (Formula ctx))
 (coreTag verifierTag : Nat) (index a b formula code : Term ctx)
 (he : Hilbert.Local U ctx G (.equal a b))
 (ha : Hilbert.Local U ctx G (accepted coreTag verifierTag index a formula code)) :
 Nonempty (Hilbert.Local U ctx G (accepted coreTag verifierTag index b formula code)) := by
 have hc (tag : Nat) : Hilbert.Local U ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index a .zero (.add formula formula) code)
   (LiteralCheckerAcceptance.coreCall tag index b .zero (.add formula formula) code)) := by
  apply LiteralRawMP.DispatcherSupportProof.callCongruence (T := U) (G := G) tag
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact .base (.logical (.reflexive _))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact he
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact .base (.logical (.reflexive _))
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact .base (.logical (.reflexive _))
        · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
          exact .base (.logical (.reflexive _))
 have hleft := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ha
 have hright := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ha
 have left := localTrans _ _ _ (.mp (.base (Logic.symmetryRule U _ _)) (hc coreTag)) hleft
 have right := localTrans _ _ _ (.mp (.base (Logic.symmetryRule U _ _)) (hc verifierTag)) hright
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) left) right⟩

/-- The fresh variable is ONLY the arithmetic gap. All original terms/formula
are weakened; existential elimination therefore cannot capture a parameter.
The certificate is independent of outer fuel and is kept exactly unchanged. -/
theorem internalize {ctx : Nat} (U : Sentence → Prop) (bound coreTag verifierTag : Nat)
 (index formula code outerFuel : Term ctx) (premise : Formula ctx)
 (h : Nonempty (Derivation U
  (.imp (GorbowPACore.weaken premise)
   (accepted coreTag verifierTag (liftTerm index) (.add (Term.numeral bound) (.var 0))
    (liftTerm formula) (liftTerm code))))) :
 Nonempty (Derivation U
  (.imp (orderGuard (Term.numeral bound) outerFuel)
   (.imp premise (accepted coreTag verifierTag index outerFuel formula code)))) := by
 let H := orderBody (Term.numeral (n := ctx) bound) outerFuel
 let P := GorbowPACore.weaken premise
 let G := [P,H]
 obtain ⟨h⟩ := h
 have hp : Hilbert.Local U (ctx+1) G P := .hypothesis List.mem_cons_self
 have hh : Hilbert.Local U (ctx+1) G
  (.equal (.add (Term.numeral bound) (.var 0)) (liftTerm outerFuel)) := by
  simpa only [G,H,orderBody,liftTerm,renameTerm,Logic.substNumeral] using
   (Hilbert.Local.hypothesis (T := U) (List.mem_cons_of_mem P (List.mem_cons_self (a := H) (l := []))))
 obtain ⟨hout⟩ := fuelTransport U G coreTag verifierTag (liftTerm index) _ _ (liftTerm formula) (liftTerm code) hh
  (.mp (.base h) hp)
 have hd := hout.discharge.discharge.finish
 have hbody : Derivation U (.imp H (GorbowPACore.weaken
  (.imp premise (accepted coreTag verifierTag index outerFuel formula code)))) := by
  simpa only [P,G,GorbowPACore.weaken,accepted,core,SixSol20261112.Fuel.success,SixSol20261112.Fuel.inputs,LiteralCheckerAcceptance.coreCall,
   GorbowFormulaSubstitution.substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   GorbowSubstitution.substitute,Logic.substNumeral,liftTerm,renameTerm] using hd
 exact HBQuantifier.existentialElimination U H
  (.imp premise (accepted coreTag verifierTag index outerFuel formula code)) ⟨hbody⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.GuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.GuardProof
