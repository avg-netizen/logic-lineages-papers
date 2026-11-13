module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionPointwiseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph
open AccumulatorBooleanInductionProof AccumulatorBooleanProof

def pointwise {ctx : Nat} (atag qtag : Nat) (index fuel context formula cert : Term ctx) : Formula ctx :=
 .imp (success qtag index fuel context formula cert)
  (.equal (accCall atag fuel index context formula cert) (.succ .zero))
def pointTemplate {ctx : Nat} (atag qtag : Nat) (index context formula cert : Term ctx) : Formula (ctx+1) :=
 pointwise atag qtag (liftTerm index) (.var 0) (liftTerm context) (liftTerm formula) (liftTerm cert)

theorem substSuccess {m n : Nat} (sub : Fin m → Term n) tag (index fuel context formula cert : Term m) :
 substituteFormula sub (success tag index fuel context formula cert) =
 success tag (substitute sub index) (substitute sub fuel) (substitute sub context) (substitute sub formula) (substitute sub cert) := by
 simp only [success,inputs,substituteFormula,Logic.substCall,Logic.substNumeral,List.Vector.map_cons,List.Vector.map_nil]
theorem pointAt {ctx : Nat} atag qtag (index context formula cert fuel : Term ctx) :
 GorbowStandardInstances.instantiate (pointTemplate atag qtag index context formula cert) fuel =
 pointwise atag qtag index fuel context formula cert := by
 simp only [GorbowStandardInstances.instantiate,pointTemplate,pointwise,substituteFormula,
  substSuccess,substAcc,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]
theorem pointNext {ctx : Nat} atag qtag (index context formula cert : Term ctx) :
 GorbowStandardInduction.successorInstance (pointTemplate atag qtag index context formula cert) =
 pointwise atag qtag (liftTerm index) (.succ (.var 0)) (liftTerm context) (liftTerm formula) (liftTerm cert) := by
 simp only [GorbowStandardInduction.successorInstance,pointTemplate,pointwise,substituteFormula,
  substSuccess,substAcc,successorLift,substitute,Fin.cases_zero]

theorem coreIntoAccumulator {n ctx : Nat} (p : Program n) (atag qtag : Nat) (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (index fuel context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (pointwise atag qtag index fuel context formula cert)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ntag := atag+1+1
 let otag := atag+GorbowPRChildTags.stepTag (base q0)+1
 have hn := normalizerNode p atag q0 ha
 have ho := orNode p atag q0 ha
 let phi := pointTemplate atag qtag index context formula cert
 obtain ⟨hzeroEq⟩ := EquationsProof.baseEquation p atag qtag ntag q0 ha hq hn index context formula cert
 obtain ⟨hzeroNorm⟩ := NormalizerProof.isOneIntro p ntag hn (call qtag (inputs index .zero context formula cert))
 have hzero : Derivation T (pointwise atag qtag index .zero context formula cert) :=
  Hilbert.compose (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ hzeroEq)) hzeroNorm
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,pointAt] using hzero
 let i := liftTerm index
 let c := liftTerm context
 let f := liftTerm formula
 let z := liftTerm cert
 let prior := accCall atag (.var 0) i c f z
 let current := call ntag (call qtag (inputs i (.succ (.var 0)) c f z) ::ᵥ nil)
 obtain ⟨hbool⟩ := accumulatorBoolean p atag qtag q0 ha hq (.var 0) i c f z
 obtain ⟨hnextEq⟩ := EquationsProof.stepEquation p atag qtag ntag otag q0 ha hq hn ho (.var 0) i c f z
 obtain ⟨hnextNorm⟩ := NormalizerProof.isOneIntro p ntag hn (call qtag (inputs i (.succ (.var 0)) c f z))
 obtain ⟨hor⟩ := NormalizerProof.orRightIntro p otag ho prior current
 have hnxt : Derivation T (pointwise atag qtag i (.succ (.var 0)) c f z) :=
  Hilbert.compose (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ hnextEq))
   (Hilbert.compose (.mp hor hbool) hnextNorm)
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  have hlocal : Hilbert.Local T (ctx+1) [phi] (pointwise atag qtag i (.succ (.var 0)) c f z) := .base hnxt
  simpa only [phi,pointNext] using Hilbert.Local.finish (Hilbert.Local.discharge hlocal)
 have hall : Derivation T (.all phi) := .mp (.mp (.arithmetic (.induction phi)) hb) (.generalize hs)
 have h := Derivation.mp (.logical (.allInstantiate phi fuel)) hall
 simpa only [phi,pointAt] using (show Nonempty (Derivation T _) from ⟨h⟩)

theorem coreIntoVerifier {n ctx : Nat} (p : Program n) (vtag qtag : Nat) (q0 : Program 5)
 (hv : (nodes p)[vtag]? = some ⟨5,verifier q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (index fuel context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (success qtag index fuel context formula cert) (success vtag index fuel context formula cert))) := by
 have ha := Equations.functionChild p vtag (accumulator q0) outerArguments hv
 obtain ⟨hc⟩ := coreIntoAccumulator p (vtag+1) qtag q0 ha hq index fuel context formula cert
 obtain ⟨he⟩ := Equations.verifierEquation p vtag q0 hv index fuel context formula cert
 exact ⟨Hilbert.compose (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ he)) hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionPointwiseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionPointwiseProof
