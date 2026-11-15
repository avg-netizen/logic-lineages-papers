module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.FirstProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformClosedSubstitutionFold UniformClosedSubstitutionFold.IterationProof
open LiteralRawMP.DispatcherSupportProof
def first {ctx : Nat} (tag : Nat) (count state raw : Term ctx) : Formula ctx :=
 .equal (iterateCall tag (.succ count) state raw)
  (iterateCall tag count (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw)
theorem substFirst {m n : Nat} (sub : Fin m → Term n) tag (count state raw : Term m) :
 substituteFormula sub (first tag count state raw) =
 first tag (substitute sub count) (substitute sub state) (substitute sub raw) := by
 simp only [first,iterateCall,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem base {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) (state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (first tag .zero state raw)) :=
 firstNumeral p tag ht 0 state raw
theorem step {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) (count state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (first tag count state raw) (first tag (.succ count) state raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := first tag count state raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hl⟩ := successor p tag ht (.succ count) state raw
 obtain ⟨hr⟩ := successor p tag ht count (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw
 have hm := callCongruence (T := T) (G := [H]) (tickTag tag)
  (iterateCall tag (.succ count) state raw ::ᵥ raw ::ᵥ nil)
  (iterateCall tag count (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw ::ᵥ raw ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hh
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base hl) (localTrans _ _ _ hm (.base (Support.equalitySymmetry _ _ hr)))))⟩
theorem internalFirst : Targets.InternalFirstTick := by
 intro n p tag ht ctx count state raw
 let phi : Formula (ctx+1) := first tag (.var 0) (liftTerm state) (liftTerm raw)
 obtain ⟨hz⟩ := base p tag ht state raw
 have hb : Derivation (GorbowPRNumeralCalculation.Theory p)
  (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substFirst,substitute,
   liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hs0⟩ := step p tag ht (.var 0 : Term (ctx+1)) (liftTerm state) (liftTerm raw)
 have hs : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substFirst,substitute,
   successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi count (induction phi hb hs)
 change Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (first tag count state raw))
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substFirst,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.FirstProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.FirstProof
