module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.MachineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.ChildrenProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformFixedFormulaAgreement.Traversal RelationalSyntaxDepthTransport.ConstructorStepTargets MachineProof

theorem unary {n ctx : Nat} (p : Program n) (I : Installation p) (G : List (Formula ctx))
 (ctor : Constructor) (hmarker : ctor ≠ .term 0)
 (bound childBound : Term ctx) (childKind : Nat) (xs value raw : Term ctx)
 (hrow : tasks I.ptag bound ctor = [LiteralSyntaxStep.taskCall I.ptag childKind childBound])
 (child : ∀ rest out : Term ctx, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I xs (.succ (HistoryLookup.consCall I.ctag
    (LiteralSyntaxStep.taskCall I.ptag childKind childBound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out value)))))
 (rest out : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I (FixedFormulaSubstitution.unaryValue I.ctag (token ctor) xs)
    (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (FixedFormulaSubstitution.unaryValue I.ctag (token ctor) value))))) := by
 let afterOut : Term ctx := HistoryAppend.appendCall I.atag out
  (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))
 obtain ⟨hfirst⟩ := MachineProof.constructor p I ctor hmarker bound rest xs out raw
 have hfirst' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (FixedFormulaSubstitution.unaryValue I.ctag (token ctor) xs)
   (input I.ptag I.ctag ctor bound rest) out raw)
   (run I xs (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag childKind childBound) rest)) afterOut raw)) := by
  simpa only [hrow,UniformFixedFormulaAgreement.StackProof.prepend,FixedFormulaSubstitution.unaryValue,afterOut] using hfirst
 obtain ⟨hchild⟩ := child rest afterOut
 obtain ⟨hout⟩ := UniformFixedFormulaAgreement.OutputProof.tokenThen p I.atag I.ctag I.ltag I.rtag
  I.ha I.hc I.hl I.hr out (Term.numeral (token ctor)) value
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := G) I.ptag (.succ rest)
  (HistoryAppend.appendCall I.atag afterOut value) (.succ rest)
  (HistoryAppend.appendCall I.atag out (FixedFormulaSubstitution.unaryValue I.ctag (token ctor) value))
  (.base (.logical (.reflexive (.succ rest)))) (.base hout)
 exact ⟨localTrans _ _ _ (.base hfirst') (localTrans _ _ _ hchild hpair)⟩

theorem binary {n ctx : Nat} (p : Program n) (I : Installation p) (G : List (Formula ctx))
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound : Term ctx) (childKind : Nat)
 (xs ys a b raw : Term ctx)
 (hrow : tasks I.ptag bound ctor = [LiteralSyntaxStep.taskCall I.ptag childKind bound,
  LiteralSyntaxStep.taskCall I.ptag childKind bound])
 (left : ∀ rest out : Term ctx, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I xs (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag childKind bound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out a)))))
 (right : ∀ rest out : Term ctx, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I ys (.succ (HistoryLookup.consCall I.ctag (LiteralSyntaxStep.taskCall I.ptag childKind bound) rest)) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag out b)))))
 (rest out : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (run I (FixedFormulaSubstitution.binaryValue I.ctag I.atag (token ctor) xs ys)
    (input I.ptag I.ctag ctor bound rest) out raw)
   (HistoryKernel.pairCall I.ptag (.succ rest)
    (HistoryAppend.appendCall I.atag out (FixedFormulaSubstitution.binaryValue I.ctag I.atag (token ctor) a b))))) := by
 let task : Term ctx := LiteralSyntaxStep.taskCall I.ptag childKind bound
 let tail := HistoryLookup.consCall I.ctag task rest
 let firstState : Term ctx := .succ (HistoryLookup.consCall I.ctag task tail)
 let afterOut : Term ctx := HistoryAppend.appendCall I.atag out (UniformClosedSubstitutionEmit.singletonValue I.ctag (Term.numeral (token ctor)))
 let afterLeft := HistoryAppend.appendCall I.atag afterOut a
 obtain ⟨hfirst⟩ := MachineProof.constructor p I ctor hmarker bound rest (HistoryAppend.appendCall I.atag xs ys) out raw
 have hfirst' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (run I (FixedFormulaSubstitution.binaryValue I.ctag I.atag (token ctor) xs ys)
    (input I.ptag I.ctag ctor bound rest) out raw)
   (run I (HistoryAppend.appendCall I.atag xs ys) firstState afterOut raw)) := by
  simpa only [hrow,UniformFixedFormulaAgreement.StackProof.prepend,FixedFormulaSubstitution.binaryValue,
   FixedFormulaSubstitution.unaryValue,task,tail,firstState,afterOut] using hfirst
 obtain ⟨hleft⟩ := left tail afterOut
 obtain ⟨hright⟩ := right rest afterLeft
 obtain ⟨hchildren⟩ := MachineProof.compose p I G xs ys
  (HistoryKernel.pairCall I.ptag firstState afterOut)
  (HistoryKernel.pairCall I.ptag (.succ tail) afterLeft)
  (HistoryKernel.pairCall I.ptag (.succ rest) (HistoryAppend.appendCall I.atag afterLeft b)) raw hleft hright
 obtain ⟨hassoc⟩ := LiteralSyntaxFrame.AppendProof.internalAppendAssociativity n p I.atag I.ctag I.ltag I.rtag
  I.ha I.hc I.hl I.hr ctx afterOut a b
 obtain ⟨htoken⟩ := UniformFixedFormulaAgreement.OutputProof.tokenThen p I.atag I.ctag I.ltag I.rtag
  I.ha I.hc I.hl I.hr out (Term.numeral (token ctor)) (HistoryAppend.appendCall I.atag a b)
 have hpair := HistoryIteratorSuffix.ReconstructionProof.pairCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := G) I.ptag (.succ rest)
  (HistoryAppend.appendCall I.atag afterLeft b) (.succ rest)
  (HistoryAppend.appendCall I.atag out (FixedFormulaSubstitution.binaryValue I.ctag I.atag (token ctor) a b))
  (.base (.logical (.reflexive (.succ rest)))) (.base (Logic.trans _ _ _ hassoc htoken))
 exact ⟨localTrans _ _ _ (.base hfirst') (localTrans _ _ _ hchildren hpair)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.ChildrenProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.ChildrenProof
