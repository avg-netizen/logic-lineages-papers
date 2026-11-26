module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionLogicProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph ExtractionLogicProof AccumulatorBooleanInductionProof

def accSuccess {ctx : Nat} (atag : Nat) (fuel index context formula cert : Term ctx) : Formula ctx :=
 .equal (accCall atag fuel index context formula cert) (Term.numeral 1)
def clause {ctx : Nat} (atag qtag : Nat) (fuel index context formula cert : Term ctx) : Formula ctx :=
 .imp (accSuccess atag fuel index context formula cert) (boundedCore qtag index fuel context formula cert)
def template {ctx : Nat} (atag qtag : Nat) (index context formula cert : Term ctx) : Formula (ctx+1) :=
 clause atag qtag (.var 0) (liftTerm index) (liftTerm context) (liftTerm formula) (liftTerm cert)
theorem substClause {m n : Nat} (sub : Fin m → Term n) atag qtag
 (fuel index context formula cert : Term m) :
 substituteFormula sub (clause atag qtag fuel index context formula cert) =
 clause atag qtag (substitute sub fuel) (substitute sub index) (substitute sub context) (substitute sub formula) (substitute sub cert) := by
 simp only [clause,accSuccess,substituteFormula,substAcc,Logic.substNumeral,substBounded]
theorem templateAt {ctx : Nat} atag qtag (index context formula cert fuel : Term ctx) :
 GorbowStandardInstances.instantiate (template atag qtag index context formula cert) fuel =
 clause atag qtag fuel index context formula cert := by
 simp only [GorbowStandardInstances.instantiate,template,substClause,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero]
theorem templateNext {ctx : Nat} atag qtag (index context formula cert : Term ctx) :
 GorbowStandardInduction.successorInstance (template atag qtag index context formula cert) =
 clause atag qtag (.succ (.var 0)) (liftTerm index) (liftTerm context) (liftTerm formula) (liftTerm cert) := by
 simp only [GorbowStandardInduction.successorInstance,template,substClause,AccumulatorBooleanInductionProof.successorLift,substitute,Fin.cases_zero]

theorem baseClause {n ctx : Nat} (p : Program n) atag qtag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (clause atag qtag .zero index context formula cert)) := by
 let nt := atag+1+1
 have hn := AccumulatorBooleanProof.normalizerNode p atag q0 ha
 obtain ⟨he⟩ := EquationsProof.baseEquation p atag qtag nt q0 ha hq hn index context formula cert
 obtain ⟨hnorm⟩ := NormalizerProof.isOneElim p nt hn (call qtag (inputs index .zero context formula cert))
 have hc := Hilbert.compose hnorm (Logic.oneTransport _ _ he)
 exact ⟨Hilbert.compose (atBound qtag index .zero context formula cert) hc⟩

theorem stepClause {n ctx : Nat} (p : Program n) atag qtag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (fuel index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (clause atag qtag fuel index context formula cert)
   (clause atag qtag (.succ fuel) index context formula cert))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let nt := atag+1+1
 let ot := atag+GorbowPRChildTags.stepTag (base q0)+1
 let previous := accCall atag fuel index context formula cert
 let current := call nt (call qtag (inputs index (.succ fuel) context formula cert) ::ᵥ nil)
 let I := clause atag qtag fuel index context formula cert
 let N := accSuccess atag (.succ fuel) index context formula cert
 let Q := boundedCore qtag index (.succ fuel) context formula cert
 have hn := AccumulatorBooleanProof.normalizerNode p atag q0 ha
 have ho := AccumulatorBooleanProof.orNode p atag q0 ha
 obtain ⟨hb⟩ := AccumulatorBooleanProof.accumulatorBoolean p atag qtag q0 ha hq fuel index context formula cert
 obtain ⟨he⟩ := EquationsProof.stepEquation p atag qtag nt ot q0 ha hq hn ho fuel index context formula cert
 obtain ⟨hsplit⟩ := NormalizerProof.orSplit p ot ho previous current
 have hsplit' := Derivation.mp hsplit hb
 have hi : Hilbert.Local T ctx [N,I] I := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hnext : Hilbert.Local T ctx [N,I] N := .hypothesis List.mem_cons_self
 have hor := Hilbert.Local.mp (.base hsplit') (.mp (.base (Logic.oneTransport _ _ he)) hnext)
 obtain ⟨hbound⟩ := boundedNext T qtag index fuel context formula cert
 have hleft : Hilbert.Local T ctx [N,I] (.imp (.equal previous (Term.numeral 1)) Q) := by
  have hp : Hilbert.Local T ctx [.equal previous (Term.numeral 1),N,I] (.equal previous (Term.numeral 1)) := .hypothesis List.mem_cons_self
  have hi' : Hilbert.Local T ctx [.equal previous (Term.numeral 1),N,I] I := .hypothesis (by simp)
  exact Hilbert.Local.discharge (.mp (.base hbound) (.mp hi' hp))
 obtain ⟨hnorm⟩ := NormalizerProof.isOneElim p nt hn (call qtag (inputs index (.succ fuel) context formula cert))
 have hright : Derivation T (.imp (.equal current (Term.numeral 1)) Q) :=
  Hilbert.compose (atBound qtag index (.succ fuel) context formula cert) hnorm
 have hout : Hilbert.Local T ctx [N,I] Q :=
  .mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hleft) (.base hright)) hor
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem accumulatorExtraction {n ctx : Nat} (p : Program n) atag qtag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (fuel index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (clause atag qtag fuel index context formula cert)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi := template atag qtag index context formula cert
 obtain ⟨hb⟩ := baseClause p atag qtag q0 ha hq index context formula cert
 obtain ⟨hs⟩ := stepClause p atag qtag q0 ha hq (.var 0 : Term (ctx+1))
  (liftTerm index) (liftTerm context) (liftTerm formula) (liftTerm cert)
 have hz : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,templateAt] using hb
 have hn : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  change Derivation T (.imp (template atag qtag index context formula cert)
    (GorbowStandardInduction.successorInstance (template atag qtag index context formula cert)))
  rw [templateNext]
  exact hs
 have hall : Derivation T (.all phi) := .mp (.mp (.arithmetic (.induction phi)) hz) (.generalize hn)
 have h := Derivation.mp (.logical (.allInstantiate phi fuel)) hall
 simpa only [phi,templateAt] using (show Nonempty (Derivation T _) from ⟨h⟩)

theorem internalExtraction : Targets.InternalExtraction := by
 intro n p vtag qtag q0 hv hq ctx index fuel context formula cert
 have ha := Equations.functionChild p vtag (accumulator q0) outerArguments hv
 obtain ⟨he⟩ := Equations.verifierEquation p vtag q0 hv index fuel context formula cert
 obtain ⟨hx⟩ := accumulatorExtraction p (vtag+1) qtag q0 ha hq fuel index context formula cert
 exact ⟨Hilbert.compose hx (Logic.oneTransport _ _ he)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.ExtractionProof
