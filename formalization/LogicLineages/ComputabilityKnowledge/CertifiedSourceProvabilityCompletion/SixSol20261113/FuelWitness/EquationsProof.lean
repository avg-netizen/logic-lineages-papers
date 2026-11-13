module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.ConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

theorem compositionCopy {n m k ctx : Nat} (p : Program n) tag ftag
 (f : Program k) (g : Fin k → Program m)
 (ht : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩)
 (hf : (nodes p)[ftag]? = some ⟨k,f⟩)
 (args : List.Vector (Term ctx) m) (values : List.Vector (Term ctx) k)
 (hv : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call (tag+argumentTag f g i) args) (values.get i)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag args) (call ftag values))) := by
 obtain ⟨he⟩ := Equations.compositionValues p tag f g ht args values hv
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tag+1) ftag k f
  (Equations.functionChild p tag f g ht) hf ctx values
 exact ⟨Logic.trans _ _ _ he hc⟩

theorem baseValue {n ctx : Nat} (p : Program n) btag qtag ntag (q0 : Program 5)
 (hb : (nodes p)[btag]? = some ⟨4,base q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,isOne⟩)
 (index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call btag (index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil))
   (call ntag (call qtag (inputs index .zero context formula cert) ::ᵥ nil)))) := by
 let args := index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil
 apply compositionCopy p btag ntag isOne (fun _ => Program.composition q0 baseArguments) hb hn args
 intro i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 let bt := btag+argumentTag isOne (fun _ => Program.composition q0 baseArguments) 0
 have ht := Equations.argumentChild p btag isOne (fun _ => Program.composition q0 baseArguments) hb 0
 apply compositionCopy p bt qtag q0 baseArguments ht hq args (inputs index .zero context formula cert)
 intro j
 have hj := Equations.argumentChild p bt q0 baseArguments ht j
 cases j using Fin.cases with
 | zero => exact Equations.projection p _ 0 hj args
 | succ j => cases j using Fin.cases with
   | zero => exact HistoryAppend.TableEquationsProof.zeroEquation p _ hj args
   | succ j => cases j using Fin.cases with
     | zero => exact Equations.projection p _ 1 hj args
     | succ j => cases j using Fin.cases with
       | zero => exact Equations.projection p _ 2 hj args
       | succ j => cases j using Fin.cases with
         | zero => exact Equations.projection p _ 3 hj args
         | succ j => exact Fin.elim0 j

theorem nextValueEquation {n ctx : Nat} (p : Program n) vtag qtag ntag (q0 : Program 5)
 (hv : (nodes p)[vtag]? = some ⟨6,nextValue q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,isOne⟩)
 (fuel previous index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call vtag (fuel ::ᵥ previous ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil))
   (call ntag (call qtag (inputs index (.succ fuel) context formula cert) ::ᵥ nil)))) := by
 let args := fuel ::ᵥ previous ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil
 apply compositionCopy p vtag ntag isOne (fun _ => Program.composition q0 nextArguments) hv hn args
 intro i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 let qt := vtag+argumentTag isOne (fun _ => Program.composition q0 nextArguments) 0
 have ht := Equations.argumentChild p vtag isOne (fun _ => Program.composition q0 nextArguments) hv 0
 apply compositionCopy p qt qtag q0 nextArguments ht hq args (inputs index (.succ fuel) context formula cert)
 intro j
 have hj := Equations.argumentChild p qt q0 nextArguments ht j
 cases j using Fin.cases with
 | zero => exact Equations.projection p _ 2 hj args
 | succ j => cases j using Fin.cases with
   | zero =>
     obtain ⟨he⟩ := Equations.compositionValues p _ .succ (fun _ => Program.projection (0 : Fin 6)) hj args (fuel ::ᵥ nil)
       (by
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact Equations.projection p _ 0 (Equations.argumentChild p _ .succ (fun _ => Program.projection (0 : Fin 6)) hj 0) args)
     obtain ⟨hs⟩ := Support.intoRegistry p .succ _
       (Equations.functionChild p _ .succ (fun _ => Program.projection (0 : Fin 6)) hj) _
       (NamedArithmeticGraph.Equations.successor _ ctx (fuel ::ᵥ nil))
     exact ⟨Logic.trans _ _ _ he hs⟩
   | succ j => cases j using Fin.cases with
     | zero => exact Equations.projection p _ 3 hj args
     | succ j => cases j using Fin.cases with
       | zero => exact Equations.projection p _ 4 hj args
       | succ j => cases j using Fin.cases with
         | zero => exact Equations.projection p _ 5 hj args
         | succ j => exact Fin.elim0 j

theorem baseEquation {n ctx : Nat} (p : Program n) atag qtag ntag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,isOne⟩)
 (index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call atag (.zero ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil))
   (call ntag (call qtag (inputs index .zero context formula cert) ::ᵥ nil)))) := by
 have hb := GorbowPRSubtree.Proof.lookupTransport n p atag ⟨5,accumulator q0⟩ 1 ⟨4,base q0⟩ ha
   (GorbowPRChildTags.Proof.recursionBase 4 (base q0) (step q0))
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p atag 4 (base q0) (step q0) ha ctx
   (index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil)
 obtain ⟨he⟩ := baseValue p (atag+1) qtag ntag q0 hb hq hn index context formula cert
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem stepEquation {n ctx : Nat} (p : Program n) atag qtag ntag otag (q0 : Program 5)
 (ha : (nodes p)[atag]? = some ⟨5,accumulator q0⟩)
 (hq : (nodes p)[qtag]? = some ⟨5,q0⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,isOne⟩)
 (ho : (nodes p)[otag]? = some ⟨2,leftOr⟩)
 (fuel index context formula cert : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call atag (.succ fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil))
   (call otag (call atag (fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) ::ᵥ
    call ntag (call qtag (inputs index (.succ fuel) context formula cert) ::ᵥ nil) ::ᵥ nil)))) := by
 let retained := index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil
 let previous := call atag (fuel ::ᵥ retained)
 let args := fuel ::ᵥ previous ::ᵥ retained
 let st := atag+stepTag (base q0)
 have hs := Equations.recursionStepChild p atag (base q0) (step q0) ha
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p atag 4 (base q0) (step q0) ha ctx fuel retained
 obtain ⟨he⟩ := compositionCopy p st otag leftOr (stepArguments q0) hs ho args
   (previous ::ᵥ call ntag (call qtag (inputs index (.succ fuel) context formula cert) ::ᵥ nil) ::ᵥ nil) (by
    intro i
    have hi := Equations.argumentChild p st leftOr (stepArguments q0) hs i
    cases i using Fin.cases with
    | zero => exact Equations.projection p _ 1 hi args
    | succ i =>
      have h : i = 0 := Fin.eq_zero i
      subst i
      exact nextValueEquation p _ qtag ntag q0 hi hq hn fuel previous index context formula cert)
 exact ⟨Logic.trans _ _ _ hr he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.EquationsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.EquationsProof
