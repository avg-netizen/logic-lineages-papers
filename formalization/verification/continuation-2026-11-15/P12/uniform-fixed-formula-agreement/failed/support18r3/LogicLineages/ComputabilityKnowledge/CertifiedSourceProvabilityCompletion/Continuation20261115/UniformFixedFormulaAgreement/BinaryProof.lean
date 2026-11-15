module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.OneTokenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.BinaryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph Traversal
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- Actual two-child order, task stack and accumulator composition. Both
induction hypotheses are instantiated at their real intermediate states. -/
theorem traverses {n ctx : Nat} (p : Program n) (I : Installation p)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound : Term ctx) (childKind : Nat)
 (xs ys : List Nat) (a b raw : Term ctx)
 (hrow : tasks I.ptag bound ctor = [LiteralSyntaxStep.taskCall I.ptag childKind bound,
  LiteralSyntaxStep.taskCall I.ptag childKind bound])
 (left : ∀ rest out : Term ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I xs (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag childKind bound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out a)))))
 (right : ∀ rest out : Term ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I ys (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag childKind bound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out b)))))
 (rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (token ctor :: (xs ++ ys)) (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (FixedFormulaSubstitution.binaryValue I.ctag I.atag (token ctor) a b))))) := by
 let task := LiteralSyntaxStep.taskCall I.ptag childKind bound
 let tail := HistoryLookup.consCall I.ctag task rest
 let firstState : Term ctx := .succ (HistoryLookup.consCall I.ctag task tail)
 let afterOut := HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))
 let afterLeft := HistoryAppend.appendCall I.atag afterOut a
 obtain ⟨hfirst⟩ := OneTokenProof.constructor p I ctor hmarker bound rest out raw
 have hfirst' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I [token ctor] (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag firstState afterOut)) := by
  simpa only [hrow,StackProof.prepend] using hfirst
 obtain ⟨hleft⟩ := left tail afterOut
 obtain ⟨hright⟩ := right rest afterLeft
 obtain ⟨hchildren⟩ := SequenceProof.compose p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.ltag I.rtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hl I.hr xs ys
  (HistoryKernel.pairCall I.ptag firstState afterOut)
  (HistoryKernel.pairCall I.ptag (.succ tail) afterLeft)
  (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag afterLeft b)) raw hleft hright
 obtain ⟨hseq⟩ := SequenceProof.compose p I.ftag I.ptag I.ctag I.stag I.etag I.atag I.ltag I.rtag
  I.hf I.hp I.hc I.hs I.he I.ha I.hl I.hr [token ctor] (xs ++ ys)
  (HistoryKernel.pairCall I.ptag (input I.ptag I.ctag ctor bound rest) out)
  (HistoryKernel.pairCall I.ptag firstState afterOut)
  (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag afterLeft b)) raw hfirst' hchildren
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity n p I.atag I.ctag I.ltag I.rtag
  I.ha I.hc I.hl I.hr ctx afterOut a b
 obtain ⟨htoken⟩ := OutputProof.tokenThen p I.atag I.ctag I.ltag I.rtag I.ha I.hc I.hl I.hr
  out (Term.numeral (token ctor)) (HistoryAppend.appendCall I.atag a b)
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) I.ptag (.succ rest) _ (.succ rest) _
  (.base (.logical (.reflexive _))) (.base (Logic.trans _ _ _ hassoc htoken))
 exact ⟨Logic.trans _ _ _ hseq hpair.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.BinaryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.BinaryProof
