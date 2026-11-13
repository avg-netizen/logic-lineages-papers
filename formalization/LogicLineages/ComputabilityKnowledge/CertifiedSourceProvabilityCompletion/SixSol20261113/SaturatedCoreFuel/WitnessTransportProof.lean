module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.WitnessTransportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAcceptance.WitnessProof

/-- Pure existential proof assembly: supplied mapping is an actual internal
body derivation, never an additional premise of core monotonicity. -/
theorem transportWitness (T : Sentence → Prop) {ctx : Nat} (ptag ctag : Nat)
 (stateA stateB requested formula : Term ctx) (H : Formula ctx)
 (hmap : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken H))
  (.imp (inner ptag ctag (liftTerm stateA) (liftTerm requested) (liftTerm formula) (.var 0))
   (inner ptag ctag (liftTerm stateB) (liftTerm requested) (liftTerm formula) (.var 0))))) :
 Nonempty (Derivation T (.imp H (.imp (witness ptag ctag stateA requested formula)
  (witness ptag ctag stateB requested formula)))) := by
 let A := inner ptag ctag (liftTerm stateA) (liftTerm requested) (liftTerm formula) (.var 0)
 let H2 := GorbowPACore.weaken (GorbowPACore.weaken H)
 let W := witness ptag ctag stateB requested formula
 have hh : Hilbert.Local T (ctx+1+1) [H2,A] H2 := .hypothesis List.mem_cons_self
 have ha : Hilbert.Local T (ctx+1+1) [H2,A] A := .hypothesis (by simp)
 have mapped := Hilbert.Local.mp (.mp (.base hmap) hh) ha
 have introduced := Hilbert.Local.mp (.base (introWitness ptag ctag
  (liftTerm (liftTerm stateB)) (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula))
  (liftTerm (.var (0 : Fin (ctx+1)))) (.var 0))) mapped
 have hin : Derivation T (.imp A (GorbowPACore.weaken
  (.imp (GorbowPACore.weaken H) (GorbowPACore.weaken W)))) := by
  simpa only [H2,W,GorbowPACore.weaken,substituteFormula,substWitness,liftTerm,renameTerm] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge introduced))
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T A
  (.imp (GorbowPACore.weaken H) (GorbowPACore.weaken W)) ⟨hin⟩
 let E := outer ptag ctag stateA requested formula
 let H1 := GorbowPACore.weaken H
 have hh1 : Hilbert.Local T (ctx+1) [H1,E] H1 := .hypothesis List.mem_cons_self
 have he1 : Hilbert.Local T (ctx+1) [H1,E] E := .hypothesis (by simp)
 have out := Hilbert.Local.mp (.mp (.base he) he1) hh1
 have hout : Derivation T (.imp E (GorbowPACore.weaken (.imp H W))) :=
  Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge out))
 obtain ⟨he2⟩ := HBQuantifier.existentialElimination T E (.imp H W) ⟨hout⟩
 let WA := witness ptag ctag stateA requested formula
 have hw : Hilbert.Local T ctx [WA,H] WA := .hypothesis List.mem_cons_self
 have hh0 : Hilbert.Local T ctx [WA,H] H := .hypothesis (by simp)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.mp (.base he2) hw) hh0)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.WitnessTransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.WitnessTransportProof
