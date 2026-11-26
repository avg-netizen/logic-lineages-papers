module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanInductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.EquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof List.Vector
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph
open AccumulatorBooleanInductionProof

theorem normalizerNode {n : Nat} (p : Program n) atag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩) :
 (nodes p)[atag+1+1]? = some ⟨1,isOne⟩ := by
 have hb : (nodes p)[atag+1]? = some ⟨4,base q0⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p atag ⟨5,accumulator q0⟩ 1 ⟨4,base q0⟩ ha
   (GorbowPRChildTags.Proof.recursionBase 4 (base q0) (step q0))
 exact Equations.functionChild p (atag+1) isOne (fun _ => .composition q0 baseArguments) hb

theorem orNode {n : Nat} (p : Program n) atag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩) :
 (nodes p)[atag+stepTag (base q0)+1]? = some ⟨2,leftOr⟩ := by
 have hs := Equations.recursionStepChild p atag (base q0) (step q0) ha
 exact Equations.functionChild p _ leftOr (stepArguments q0) hs

noncomputable def booleanTransport {T : Sentence → Prop} {ctx : Nat} (a b : Term ctx)
 (he : Derivation T (.equal a b)) : Derivation T (.imp (boolean a) (boolean b)) := by
 have hr := Derivation.mp (.logical (.equalityReplace (boolean (.var 0)) a b)) he
 simpa only [GorbowStandardInstances.instantiate,substBoolean,GorbowSubstitution.substitute,Fin.cases_zero] using hr

theorem accumulatorBoolean {n ctx : Nat} (p : Program n) atag qtag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (fuel index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (boolean (accCall atag fuel index context formula cert))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ntag := atag+1+1
 let otag := atag+stepTag (base q0)+1
 have hn := normalizerNode p atag q0 ha
 have ho := orNode p atag q0 ha
 obtain ⟨he0⟩ := EquationsProof.baseEquation p atag qtag ntag q0 ha hq hn index context formula cert
 obtain ⟨hb0⟩ := NormalizerProof.isOneBoolean p ntag hn (call qtag (inputs index .zero context formula cert))
 have hb : Derivation T (boolean (accCall atag .zero index context formula cert)) :=
  .mp (booleanTransport _ _ (Support.equalitySymmetry _ _ he0)) hb0
 let i := liftTerm index
 let c := liftTerm context
 let f := liftTerm formula
 let z := liftTerm cert
 let prior := accCall atag (.var 0) i c f z
 let current := call ntag (call qtag (inputs i (.succ (.var 0)) c f z) ::ᵥ nil)
 obtain ⟨hes⟩ := EquationsProof.stepEquation p atag qtag ntag otag q0 ha hq hn ho (.var 0) i c f z
 obtain ⟨hc⟩ := NormalizerProof.isOneBoolean p ntag hn (call qtag (inputs i (.succ (.var 0)) c f z))
 obtain ⟨hor⟩ := NormalizerProof.orBoolean p otag ho prior current
 have hh : Hilbert.Local T (ctx+1) [boolean prior] (boolean prior) := .hypothesis List.mem_cons_self
 have hstep : Hilbert.Local T (ctx+1) [boolean prior] (boolean (accCall atag (.succ (.var 0)) i c f z)) :=
  .mp (.base (booleanTransport _ _ (Support.equalitySymmetry _ _ hes))) (.mp (.mp (.base hor) hh) (.base hc))
 exact inductionFromBaseStep T atag index context formula cert fuel hb
  (Hilbert.Local.finish (Hilbert.Local.discharge hstep))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.AccumulatorBooleanProof
