module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.RetrievalProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph TableEquationsProof TableLookupProof AppendEquationsProof ValueEquationsProof RetrievalProof

noncomputable def binaryCongruence {T : Sentence → Prop} {ctx : Nat} tag (a a' b b' : Term ctx)
    (ha : Derivation T (.equal a a')) (hb : Derivation T (.equal b b')) :
    Derivation T (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (call tag (a' ::ᵥ b' ::ᵥ nil))) := by
  have h1 := Logic.unary (call tag (.var 0 ::ᵥ liftTerm b ::ᵥ nil)) _ _ ha
  have h2 := Logic.unary (call tag (liftTerm a' ::ᵥ .var 0 ::ᵥ nil)) _ _ hb
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at h1 h2
  exact Logic.trans _ _ _ h1 h2

def valueAt (tag : Nat) := valueTag (tableTag tag)
def outputConsTag (tag : Nat) := valueAt tag+1
def inputHeadTag (tag : Nat) := headWrapper (valueAt tag)+1
def inputTailTag (tag : Nat) := tailWrapper (valueAt tag)+1

/-- Unrestricted positive-code recursion law. No reconstruction or coded-list
premise: the actual decoder bound alone pays course-of-values coverage. -/
theorem appendPositive {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,append⟩) (count right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (appendCall tag (.succ count) right)
        (HistoryLookup.consCall (outputConsTag tag)
          (call (inputHeadTag tag) (.succ count ::ᵥ nil))
          (appendCall tag (call (inputTailTag tag) (.succ count ::ᵥ nil)) right)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let tt := tableTag tag
  let vt := valueAt tag
  let child := call (inputTailTag tag) (.succ count ::ᵥ nil)
  let hdval := call (inputHeadTag tag) (.succ count ::ᵥ nil)
  let previous := tableCall tt count right
  have htab := tableInstalled p tag ht
  have hv := valueInstalled p tt htab
  obtain ⟨hc,hh,htail,hd,hl,hp⟩ := valueNodes p vt hv
  obtain ⟨ha⟩ := appendEquation p tag ht (.succ count) right
  obtain ⟨hs⟩ := tableSuccessor p tt htab count right
  obtain ⟨hhead⟩ := HistoryLookup.DestructorProof.internalHeadCons n p (tag+1) (consTag tt)
    (headInstalled p tag ht) (consInstalled p tt htab) ctx (entryCall tt count previous right) previous
  have htop := Logic.trans _ _ _ ha (Logic.trans _ _ _
    (HistoryLookup.DestructorProof.unaryCallCongruence (tag+1) _ _ hs) hhead)
  obtain ⟨he⟩ := valueEquation p vt hv count previous right
  obtain ⟨hbound⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p (inputTailTag tag) htail ctx count
  obtain ⟨hget⟩ := tableRetrieve p tt (lookupWrapper vt+1) (tag+1) (differenceWrapper vt+1) (predWrapper vt+1)
    htab hl (headInstalled p tag ht) hd hp count child right
  have hrecursive := Derivation.mp hget hbound
  obtain ⟨hrecAppend⟩ := appendEquation p tag ht child right
  have hresult := Logic.trans _ _ _ hrecursive (Support.equalitySymmetry _ _ hrecAppend)
  have hcons := binaryCongruence (outputConsTag tag) hdval hdval _ _ (.logical (.reflexive hdval)) hresult
  exact ⟨Logic.trans _ _ _ htop (Logic.trans _ _ _ he hcons)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveProof
