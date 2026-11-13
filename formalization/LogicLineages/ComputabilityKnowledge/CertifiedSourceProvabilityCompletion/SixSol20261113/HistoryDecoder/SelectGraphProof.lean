module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.SelectGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def graph {ctx : Nat} (tag : Nat) (test yes no : Term ctx) : Formula ctx :=
  .disj (.equal (call tag (test ::ᵥ yes ::ᵥ no ::ᵥ nil)) no)
    (.conj (.equal test .zero) (.equal (call tag (test ::ᵥ yes ::ᵥ no ::ᵥ nil)) yes))

theorem substituteGraph {m n : Nat} (sub : Fin m → Term n) tag (test yes no : Term m) :
    substituteFormula sub (graph tag test yes no) =
      graph tag (substitute sub test) (substitute sub yes) (substitute sub no) := by
  simp only [graph,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]

noncomputable def testCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (s t yes no : Term ctx) (h : Hilbert.Local T ctx G (.equal s t)) :
    Hilbert.Local T ctx G (.equal (call tag (s ::ᵥ yes ::ᵥ no ::ᵥ nil))
      (call tag (t ::ᵥ yes ::ᵥ no ::ᵥ nil))) := by
  have d := localUnary (call tag (.var 0 ::ᵥ liftTerm yes ::ᵥ liftTerm no ::ᵥ nil)) s t h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,
    Support.shiftCancel,substitute,Fin.cases_zero] using d

theorem selectGraph {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test yes no : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (graph tag test yes no)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hz⟩ := HistoryCodec.PairProof.selectZero p tag ht yes no
  have hzero : Derivation T (.imp (.equal test .zero) (graph tag test yes no)) := by
    have h : Hilbert.Local T ctx [.equal test .zero] (.equal test .zero) := .hypothesis List.mem_cons_self
    have he := localTrans _ _ _ (testCongruence tag test .zero yes no h) (.base hz)
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (.mp (.base (.logical (.orRight _ _)))
        (.mp (.mp (.base (.logical (.andIntro _ _))) h) he)))
  let H := HistoryOrder.SupportProof.predBody test
  obtain ⟨hp⟩ := HistoryCodec.PairProof.selectPositive p tag ht (liftTerm yes) (liftTerm no) (.var 0)
  have h : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm test) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  have he := localTrans _ _ _ (testCongruence tag (liftTerm test) (.succ (.var 0)) (liftTerm yes) (liftTerm no) h) (.base hp)
  have hg : Hilbert.Local T (ctx+1) [H] (graph tag (liftTerm test) (liftTerm yes) (liftTerm no)) :=
    .mp (.base (.logical (.orLeft _ _))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (graph tag test yes no))) := by
    simpa only [GorbowPACore.weaken,substituteGraph,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge hg)
  obtain ⟨hpositive⟩ := HBQuantifier.existentialElimination T H (graph tag test yes no) ⟨hbody⟩
  obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T test
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpositive) hsplit⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.SelectGraphProof
