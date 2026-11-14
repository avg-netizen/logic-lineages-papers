module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.RightProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof

theorem internalReplacement : Targets.InternalRight := by
 intro n p old a x I ctx t u v index fuel
 obtain ⟨scanTag,hscan⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p I.validatorTag I.hv
 obtain ⟨_,_,_,rightTag,_,_,_,hright⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 have hhead := Equations.functionChild p I.appendTag HistoryLookup.head (fun _ : Fin 1 => HistoryAppend.table) I.ha
 have hleft := Equations.functionChild p (I.appendTag+1) (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => HistoryCodec.predecessor) hhead
 let J : RawAddRightAcceptance.Installation p (RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)) := {
  testTag := I.addRightTestTag, searchTag := I.addRightSearchTag, dropTag := I.dropTag,
  ht := I.haddRightTest, hs := I.haddRightSearch, hd := I.hdrop,
  lengthTag := I.lengthTag, appendTag := I.appendTag, consTag := I.consTag,
  hl := I.hlength, ha := I.ha, hc := I.hc,
  qtag := I.addRightLineTag, logicalTag := I.addRightTag, pairTag := I.pairTag,
  validatorTag := I.validatorTag, leftDecoderTag := I.appendTag+1+1, rightDecoderTag := rightTag,
  hq := I.haddRightLine, hlogical := I.haddRight, hp := I.hp, hv := I.hv,
  hleft := hleft, hright := hright }
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid I.validatorTag t
 let W := RawReflexivityDispatcher.valid I.validatorTag u
 let Z := RawReflexivityDispatcher.valid I.validatorTag v
 let G := [Z,W,V]
 have ht : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hu : Hilbert.Local T ctx G W := .hypothesis (by simp [G])
 have hv : Hilbert.Local T ctx G Z := .hypothesis List.mem_cons_self
 obtain ⟨hlog⟩ := RawAddRightAcceptance.StatementChecks.exactLogical n p _ J ctx t u v
 have haccepted := Hilbert.Local.mp (.mp (.mp (.base hlog) ht) hu) hv
 obtain ⟨hq⟩ := RawAddRightReplace.StatementChecks.exactInternalLine n p I.addRightLineTag I.pairTag I.consTag I.appendTag
  I.haddRightLine I.hp I.hc I.ha ctx t u v
 obtain ⟨hal⟩ := RawAddLeftRetention.StatementChecks.exactRetention n p (RawAddLeftCongruence.previousLogical old)
  I.addRightTag I.addLeftTag I.haddRight I.haddLeft ctx (RawAddRightReplace.lineCall I.addRightLineTag t u v)
 have hleft := Hilbert.Local.mp (.base hal) haccepted
 obtain ⟨hmr⟩ := RawMulRightRetention.StatementChecks.exactRetention n p (RawMulRightCongruence.previousLogical old)
  I.addLeftTag I.previousTag I.haddLeft I.hprevious ctx (RawAddRightReplace.lineCall I.addRightLineTag t u v)
 have hprevious := Hilbert.Local.mp (.base hmr) hleft
 have he := HistoryLookup.DestructorProof.unaryCallCongruence I.previousTag _ _ hq
 have hleaf := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ he)) hprevious
 obtain ⟨hvalid⟩ := RawAddRightDispatcher.StatementChecks.exactValidity n p I.validatorTag I.ftag I.pairTag I.consTag I.appendTag
  I.hv I.hf I.hp I.hc I.ha ctx t u v
 let formula := RawAddRightReplace.formulaValue I.consTag I.appendTag t u v
 let args := HistoryLookup.consCall I.consTag (RawAddRightReplace.templateValue I.consTag I.appendTag t v)
  (HistoryLookup.consCall I.consTag t (HistoryLookup.consCall I.consTag u .zero))
 obtain ⟨hc⟩ := RawMulLeftRetention.StatementChecks.exactCoreRetention n p (RawMulLeftCongruence.previousLogical old) (RawMulNewestAddition.arithmetic a) x
  (RawMulLeftCongruence.ReflexivityProof.retentionInstallation p old (RawMulNewestAddition.arithmetic a) x I.toCurrent.toComputation.toEvaluator.toAddition.toCongruence.toNewestEquality.toCongruences.toNewest)
  ctx formula (Term.numeral 12) args index fuel
 have hcore := Hilbert.Local.mp (.mp (.base hc) (.mp (.mp (.mp (.base hvalid) ht) hu) hv)) hleaf
 have hcert := HistoryAppend.PositiveProof.binaryCongruence I.consTag _ _ (.zero : Term ctx) .zero hq (.logical (.reflexive .zero))
 have hcg := callCongruence (T := T) (G := G) I.qctag
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ RawAddRightCertificate.certificate I.consTag I.addRightLineTag t u v ::ᵥ nil)
  (index ::ᵥ fuel ::ᵥ .zero ::ᵥ .add formula formula ::ᵥ RawMulLeftRetention.certificate I.pairTag I.consTag formula (Term.numeral 12) args ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive _))
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive _))
       | succ i => cases i using Fin.cases with
         | zero => exact .base (.logical (.reflexive _))
         | succ i => cases i using Fin.cases with
           | zero => exact .base hcert
           | succ i => exact Fin.elim0 i)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ hcg hcore))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.RightProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.RightProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.RightProof.internalReplacement
