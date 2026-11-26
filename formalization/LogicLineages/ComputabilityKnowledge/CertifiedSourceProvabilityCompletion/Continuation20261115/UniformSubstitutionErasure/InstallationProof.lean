module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.InstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113 SixSol20261112.Fuel HistoryRuleSuffix List.Vector
theorem auxiliaries {n : Nat} (p : Program n) (etag ntag : Nat)
 (he : (nodes p)[etag]? = some ⟨1,eraseCode⟩)
 (hn : (nodes p)[ntag]? = some ⟨2,UniformClosedSubstitutionFold.tick⟩) :
 ∃ (ptag ctag stag emitTag atag htag ttag ltag rtag : Nat),
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ ∧
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ ∧
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ ∧
 (nodes p)[emitTag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ ∧
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ ∧
 (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩ ∧
 (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩ ∧
 (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ ∧
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ := by
 let eg : Fin 2 → Program 1 := Fin.cases (HistoryDecoder.decoder false) (Fin.cases syntaxProjection Fin.elim0)
 have hp := Equations.functionChild p etag HistoryCodec.pair eg he
 have hl := Equations.argumentChild p etag HistoryCodec.pair eg he 0
 have hsp := Equations.argumentChild p etag HistoryCodec.pair eg he 1
 let spTag := etag + argumentTag HistoryCodec.pair eg 1
 have hr := Equations.argumentChild p spTag (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => HistoryDecoder.decoder true) hsp 0
 let branch : Program 2 := applyTwo HistoryCodec.pair
  (applyOne HistoryLookup.tail UniformClosedSubstitutionFold.remaining) UniformClosedSubstitutionFold.advanced
 let ng : Fin 3 → Program 2 := Fin.cases UniformClosedSubstitutionFold.remaining
  (Fin.cases (.projection 0) (Fin.cases branch Fin.elim0))
 have hb := Equations.argumentChild p ntag HistoryCodec.select ng hn 2
 let btag := ntag + argumentTag HistoryCodec.select ng 2
 let bg : Fin 2 → Program 2 := Fin.cases (applyOne HistoryLookup.tail UniformClosedSubstitutionFold.remaining)
  (Fin.cases UniformClosedSubstitutionFold.advanced Fin.elim0)
 have htail := Equations.argumentChild p btag HistoryCodec.pair bg hb 0
 let tailTag := btag + argumentTag HistoryCodec.pair bg 0
 have ht := Equations.functionChild p tailTag HistoryLookup.tail
  (fun _ : Fin 1 => UniformClosedSubstitutionFold.remaining) htail
 have hadv := Equations.argumentChild p btag HistoryCodec.pair bg hb 1
 let advTag := btag + argumentTag HistoryCodec.pair bg 1
 let ag : Fin 3 → Program 2 := fun i =>
  (UniformClosedSubstitutionFold.accumulator ::ᵥ applyOne HistoryLookup.head UniformClosedSubstitutionFold.remaining ::ᵥ (.projection 1) ::ᵥ nil).get i
 have hsub := Equations.functionChild p advTag UniformClosedSubstitutionFold.subStepCode ag hadv
 have hhead := Equations.argumentChild p advTag UniformClosedSubstitutionFold.subStepCode ag hadv 1
 let headTag := advTag + argumentTag UniformClosedSubstitutionFold.subStepCode ag 1
 have hh := Equations.functionChild p headTag HistoryLookup.head
  (fun _ : Fin 1 => UniformClosedSubstitutionFold.remaining) hhead
 let sg : Fin 2 → Program 3 := Fin.cases
  (applyTwo LiteralSyntaxStep.stepCode UniformClosedSubstitutionFold.syntaxState (.projection 1))
  (Fin.cases (applyTwo HistoryAppend.append UniformClosedSubstitutionFold.output UniformClosedSubstitutionFold.emitted) Fin.elim0)
 let subTag := advTag+1
 have hstep := Equations.argumentChild p subTag HistoryCodec.pair sg hsub 0
 let stepTag0 := subTag + argumentTag HistoryCodec.pair sg 0
 have hs := Equations.functionChild p stepTag0 LiteralSyntaxStep.stepCode
  (Fin.cases UniformClosedSubstitutionFold.syntaxState (Fin.cases (.projection (1 : Fin 3)) Fin.elim0)) hstep
 have happ := Equations.argumentChild p subTag HistoryCodec.pair sg hsub 1
 let appTag := subTag + argumentTag HistoryCodec.pair sg 1
 let apg : Fin 2 → Program 3 := Fin.cases UniformClosedSubstitutionFold.output
  (Fin.cases UniformClosedSubstitutionFold.emitted Fin.elim0)
 have ha := Equations.functionChild p appTag HistoryAppend.append apg happ
 have hem := Equations.argumentChild p appTag HistoryAppend.append apg happ 1
 let emTag := appTag + argumentTag HistoryAppend.append apg 1
 let emg : Fin 3 → Program 3 := fun i =>
  (UniformClosedSubstitutionFold.syntaxState ::ᵥ (.projection 1) ::ᵥ (.projection 2) ::ᵥ nil).get i
 have hm := Equations.functionChild p emTag UniformClosedSubstitutionEmit.emitCode emg hem
 let emitTag := emTag+1
 let eg0 : Fin 3 → Program 3 := Fin.cases (.projection 0)
  (Fin.cases UniformClosedSubstitutionEmit.singletonCode
   (Fin.cases (choose UniformClosedSubstitutionEmit.stackCode UniformClosedSubstitutionEmit.singletonCode UniformClosedSubstitutionEmit.activeCode) Fin.elim0))
 have hsingle := Equations.argumentChild p emitTag HistoryCodec.select eg0 hm 1
 let singleTag := emitTag + argumentTag HistoryCodec.select eg0 1
 have hc := Equations.functionChild p singleTag HistoryCodec.cons
  (Fin.cases (.projection (1 : Fin 3)) (Fin.cases (constant 3 0) Fin.elim0)) hsingle
 exact ⟨etag+1,singleTag+1,stepTag0+1,emitTag,appTag+1,headTag+1,tailTag+1,
  etag+argumentTag HistoryCodec.pair eg 0,
  spTag+argumentTag (HistoryDecoder.decoder false) (fun _ : Fin 1 => HistoryDecoder.decoder true) 0,
  hp,hc,hs,hm,ha,hh,ht,hl,hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionErasure.InstallationProof
