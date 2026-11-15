module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OneTokenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.UnaryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph Traversal
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- Structural composition for an actual one-child row. The child derivation
is the private induction hypothesis, never a premise of the frozen endpoint. -/
theorem traverses {n ctx : Nat} (p : Program n) (I : Installation p)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0)
 (bound childBound : Term ctx) (childKind : Nat) (xs : List Nat) (value raw : Term ctx)
 (hrow : tasks I.ptag bound ctor = [LiteralSyntaxStep.taskCall I.ptag childKind childBound])
 (child : ∀ rest out : Term ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I xs (.succ (HistoryLookup.consCall I.ctag
    (LiteralSyntaxStep.taskCall I.ptag childKind childBound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out value)))))
 (rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (token ctor :: xs) (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out
     (FixedFormulaSubstitution.unaryValue I.ctag (token ctor) value))))) := by
 let single : Term ctx := UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor))
 let afterOut := HistoryAppend.appendCall I.atag out single
 let childState : Term ctx := .succ (HistoryLookup.consCall I.ctag
  (LiteralSyntaxStep.taskCall I.ptag childKind childBound) rest)
 obtain ⟨hfirst⟩ := OneTokenProof.constructor p I ctor hmarker bound rest out raw
 have hfirst' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I [token ctor] (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag childState afterOut)) := by
  simpa only [hrow,StackProof.prepend] using hfirst
 obtain ⟨hchild⟩ := child rest afterOut
 obtain ⟨hseq⟩ := SequenceProof.compose p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.ltag I.rtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hl I.hr [token ctor] xs
  (HistoryKernel.pairCall I.ptag (input I.ptag I.ctag ctor bound rest) out)
  (HistoryKernel.pairCall I.ptag childState afterOut)
  (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag afterOut value)) raw hfirst' hchild
 obtain ⟨hout⟩ := OutputProof.tokenThen p I.atag I.ctag I.ltag I.rtag I.ha I.hc I.hl I.hr
  out (Term.numeral (token ctor)) value
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag (.succ rest) _ (.succ rest) _
  (.base (.logical (.reflexive _))) (.base hout)
 exact ⟨Logic.trans _ _ _ hseq hpair.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.UnaryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.UnaryProof
