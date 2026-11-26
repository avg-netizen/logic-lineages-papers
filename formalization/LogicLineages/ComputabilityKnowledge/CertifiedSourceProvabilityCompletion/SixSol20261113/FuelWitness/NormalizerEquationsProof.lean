module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualEquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.SelectGraphProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

def unary {ctx : Nat} (tag : Nat) (t : Term ctx) := call tag (t ::ᵥ nil)
def binary {ctx : Nat} (tag : Nat) (s t : Term ctx) := call tag (s ::ᵥ t ::ᵥ nil)
def oneStep : Program 2 := .composition isZero (fun _ => .projection (0 : Fin 2))
def zeroChild (tag : Nat) := tag + stepTag (Program.zero) + 1

theorem baseChild {n m : Nat} (p : Program n) tag (f : Program m) (g : Program (m+2))
 (ht : (nodes p)[tag]? = some ⟨m+1,Program.recursion f g⟩) :
 (nodes p)[tag+1]? = some ⟨m,f⟩ :=
 GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m+1,Program.recursion f g⟩ 1 ⟨m,f⟩ ht
  (GorbowPRChildTags.Proof.recursionBase m f g)

theorem isZeroZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isZero⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unary tag (.zero : Term ctx)) (.succ .zero))) := by
 have hb := baseChild p tag (oneProgram 0) (zeroProgram 2) ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 0 (oneProgram 0) (zeroProgram 2) ht ctx nil
 obtain ⟨he⟩ := HistoryKernel.EqualEquationsProof.oneEquation p (tag+1) hb (nil : List.Vector (Term ctx) 0)
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem isZeroSucc {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isZero⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unary tag (.succ t)) .zero)) := by
 have hs := Equations.recursionStepChild p tag (oneProgram 0) (zeroProgram 2) ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 0 (oneProgram 0) (zeroProgram 2) ht ctx t nil
 obtain ⟨he⟩ := HistoryAppend.TableEquationsProof.zeroEquation p _ hs (t ::ᵥ unary tag t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem zeroInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) :
 (nodes p)[zeroChild tag]? = some ⟨1,isZero⟩ :=
 Equations.functionChild p _ isZero (fun _ => .projection (0 : Fin 2))
  (Equations.recursionStepChild p tag .zero oneStep ht)

theorem isOneZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unary tag (.zero : Term ctx)) .zero)) := by
 have hb := baseChild p tag .zero oneStep ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 0 .zero oneStep ht ctx nil
 obtain ⟨he⟩ := Support.intoRegistry p .zero (tag+1) hb _ (NamedArithmeticGraph.Equations.zero (tag+1) ctx)
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem isOneSucc {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unary tag (.succ t)) (unary (zeroChild tag) t))) := by
 have hs := Equations.recursionStepChild p tag .zero oneStep ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 0 .zero oneStep ht ctx t nil
 obtain ⟨he⟩ := Equations.compositionValues p _ isZero (fun _ => .projection (0 : Fin 2)) hs
  (t ::ᵥ unary tag t ::ᵥ nil) (t ::ᵥ nil)
  (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact Equations.projection p _ (0 : Fin 2) (Equations.argumentChild p _ isZero (fun _ => .projection (0 : Fin 2)) hs 0) _)
 exact ⟨Logic.trans _ _ _ hr he⟩

theorem isOneOne {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,isOne⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unary tag (.succ .zero : Term ctx)) (.succ .zero))) := by
 obtain ⟨hs⟩ := isOneSucc p tag ht (.zero : Term ctx)
 obtain ⟨hz⟩ := isZeroZero (ctx := ctx) p _ (zeroInstalled p tag ht)
 exact ⟨Logic.trans _ _ _ hs hz⟩

theorem orZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,leftOr⟩) (t : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (binary tag .zero t) t)) := by
 let f := Program.projection (0 : Fin 1)
 let g : Program 3 := .composition .succ (fun _ => .projection (0 : Fin 3))
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 f g ht ctx (t ::ᵥ nil)
 obtain ⟨he⟩ := Equations.projection p (tag+1) (0 : Fin 1) (baseChild p tag f g ht) (t ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hr he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.NormalizerEquationsProof
