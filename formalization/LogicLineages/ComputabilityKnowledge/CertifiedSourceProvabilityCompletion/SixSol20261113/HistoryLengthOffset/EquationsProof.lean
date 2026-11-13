module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

def countCall {ctx : Nat} (tag : Nat) (bound code : Term ctx) : Term ctx := call tag (bound ::ᵥ code ::ᵥ nil)
def selectCall {ctx : Nat} (tag : Nat) (test a b : Term ctx) : Term ctx := call tag (test ::ᵥ a ::ᵥ b ::ᵥ nil)
def stepArguments : Fin 3 → Program 3 :=
  Fin.cases suffixAt (Fin.cases (.projection 1) (Fin.cases (applyOne .succ (.projection 1)) Fin.elim0))
def suffixArguments : Fin 2 → Program 3 := Fin.cases (.projection 0) (Fin.cases (.projection 2) Fin.elim0)
def st (tag : Nat) := tag+stepTag (zeroProgram 1)
def dtag (tag : Nat) := st tag+argumentTag HistoryCodec.select stepArguments 0+1
def stag (tag : Nat) := st tag+1

theorem substCount {m n : Nat} (sub : Fin m → Term n) tag (bound code : Term m) :
    substitute sub (countCall tag bound code)=countCall tag (substitute sub bound) (substitute sub code) := by
  simp only [countCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substSelect {m n : Nat} (sub : Fin m → Term n) tag (test a b : Term m) :
    substitute sub (selectCall tag test a b)=selectCall tag (substitute sub test) (substitute sub a) (substitute sub b) := by
  simp only [selectCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem countNodes {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,count⟩) :
    (nodes p)[dtag tag]? = some ⟨2,HistoryLookup.drop⟩ ∧
    (nodes p)[stag tag]? = some ⟨3,HistoryCodec.select⟩ := by
  have hs := Equations.recursionStepChild p tag (zeroProgram 1) countStep ht
  have hd := Equations.argumentChild p (st tag) HistoryCodec.select stepArguments hs 0
  exact ⟨Equations.functionChild p _ HistoryLookup.drop suffixArguments hd,
    Equations.functionChild p _ HistoryCodec.select stepArguments hs⟩

theorem countZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,count⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (countCall tag .zero code) .zero)) := by
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,count⟩ 1 ⟨1,zeroProgram 1⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 (zeroProgram 1) countStep)
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 (zeroProgram 1) countStep ht ctx (code ::ᵥ nil)
  obtain ⟨hb⟩ := HistoryAppend.TableEquationsProof.zeroEquation p (tag+1) hb (code ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hz hb⟩

theorem suffixEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,suffixAt⟩) (i previous code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (i ::ᵥ previous ::ᵥ code ::ᵥ nil)) (HistoryLookup.DropEquationsProof.dropCall (tag+1) i code))) := by
  exact HistoryAppend.ValueEquationsProof.binaryValues p tag HistoryLookup.drop suffixArguments ht _ i code
    (Equations.projection p _ (0 : Fin 3) (Equations.argumentChild p tag _ suffixArguments ht 0) _)
    (Equations.projection p _ (2 : Fin 3) (Equations.argumentChild p tag _ suffixArguments ht 1) _)

theorem countSuccessor {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,count⟩) (bound code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (countCall tag (.succ bound) code)
        (selectCall (stag tag) (HistoryLookup.DropEquationsProof.dropCall (dtag tag) bound code)
          (countCall tag bound code) (.succ (countCall tag bound code))))) := by
  let av := bound ::ᵥ countCall tag bound code ::ᵥ code ::ᵥ nil
  have hs := Equations.recursionStepChild p tag (zeroProgram 1) countStep ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1 (zeroProgram 1) countStep ht ctx bound (code ::ᵥ nil)
  have h0 := Equations.argumentChild p (st tag) HistoryCodec.select stepArguments hs 0
  have h1 := Equations.argumentChild p (st tag) HistoryCodec.select stepArguments hs 1
  have h2 := Equations.argumentChild p (st tag) HistoryCodec.select stepArguments hs 2
  obtain ⟨he⟩ := HistoryKernel.TransitionEquationsProof.threeValues p (st tag) HistoryCodec.select stepArguments hs av
    (HistoryLookup.DropEquationsProof.dropCall (dtag tag) bound code) (countCall tag bound code) (.succ (countCall tag bound code))
    (suffixEquation p _ h0 bound (countCall tag bound code) code)
    (Equations.projection p _ (1 : Fin 3) h1 av)
    (HistoryDecoder.OuterEquationsProof.successorProjection p _ (1 : Fin 3) h2 av)
  exact ⟨Logic.trans _ _ _ hr he⟩

theorem lengthEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,lengthProgram⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (lengthCall tag code) (countCall (tag+1) code code))) := by
  apply HistoryAppend.ValueEquationsProof.binaryValues p tag count (fun _ : Fin 2 => .projection 0) ht _ code code
  · exact Equations.projection p _ (0 : Fin 1) (Equations.argumentChild p tag count (fun _ : Fin 2 => .projection 0) ht 0) _
  · exact Equations.projection p _ (0 : Fin 1) (Equations.argumentChild p tag count (fun _ : Fin 2 => .projection 0) ht 1) _

theorem internalLengthNil : Targets.InternalLengthNil := by
  intro n p tag ht ctx
  have hc := Equations.functionChild p tag count (fun _ : Fin 2 => .projection 0) ht
  obtain ⟨hl⟩ := lengthEquation p tag ht (.zero : Term ctx)
  obtain ⟨hz⟩ := countZero p (tag+1) hc (.zero : Term ctx)
  exact ⟨Logic.trans _ _ _ hl hz⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.EquationsProof
