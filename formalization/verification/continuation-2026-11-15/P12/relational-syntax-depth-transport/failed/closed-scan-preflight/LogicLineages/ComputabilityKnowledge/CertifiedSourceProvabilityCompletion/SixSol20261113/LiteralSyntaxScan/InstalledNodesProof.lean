module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.ScanBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

theorem scanNodes {n : Nat} (p : Program n) (stag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,scanCode⟩) :
 ∃ (itag ltag ptag rtag : Nat),
 (nodes p)[itag]? = some ⟨2,iterator⟩ ∧
 (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ ∧
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ ∧
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ := by
 let outer : Fin 1 → Program 2 := fun _ => finalState
 have hr := Equations.functionChild p stag (HistoryDecoder.decoder true) outer hs
 have hf := Equations.argumentChild p stag (HistoryDecoder.decoder true) outer hs 0
 let ftag := stag + argumentTag (HistoryDecoder.decoder true) outer 0
 let fs : Fin 2 → Program 2 := Fin.cases
  (applyOne HistoryLengthOffset.lengthProgram (.projection 1)) (Fin.cases initial Fin.elim0)
 have hi := Equations.functionChild p ftag iterator fs hf
 have hlw := Equations.argumentChild p ftag iterator fs hf 0
 have hpw := Equations.argumentChild p ftag iterator fs hf 1
 let lw := ftag + argumentTag iterator fs 0
 let pw := ftag + argumentTag iterator fs 1
 have hl := Equations.functionChild p lw HistoryLengthOffset.lengthProgram (fun _ : Fin 1 => .projection (1 : Fin 2)) hlw
 let initArgs : Fin 2 → Program 2 := Fin.cases (.projection 1)
  (Fin.cases (applyOne .succ (.projection 0)) Fin.elim0)
 have hp := Equations.functionChild p pw HistoryCodec.pair initArgs hpw
 exact ⟨ftag+1,lw+1,pw+1,stag+1,hi,hl,hp,hr⟩

theorem stepNode {n : Nat} (p : Program n) (itag : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,iterator⟩) :
 ∃ (stag : Nat), (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩ := by
 let tt := IterationEquationsProof.tickTag itag
 have ht := IterationEquationsProof.tickInstalled p itag hi
 let no := applyTwo HistoryCodec.pair (applyOne HistoryLookup.tail remaining)
  (applyTwo LiteralSyntaxStep.stepCode taskState (applyOne HistoryLookup.head remaining))
 let g : Fin 3 → Program 1 := Fin.cases remaining (Fin.cases (.projection 0) (Fin.cases no Fin.elim0))
 have hn := Equations.argumentChild p tt HistoryCodec.select g ht 2
 let nt := tt + argumentTag HistoryCodec.select g 2
 let ng : Fin 2 → Program 1 := Fin.cases (applyOne HistoryLookup.tail remaining)
  (Fin.cases (applyTwo LiteralSyntaxStep.stepCode taskState (applyOne HistoryLookup.head remaining)) Fin.elim0)
 have hw := Equations.argumentChild p nt HistoryCodec.pair ng hn 1
 let sw := nt + argumentTag HistoryCodec.pair ng 1
 let sg : Fin 2 → Program 1 := Fin.cases taskState (Fin.cases (applyOne HistoryLookup.head remaining) Fin.elim0)
 exact ⟨sw+1, Equations.functionChild p sw LiteralSyntaxStep.stepCode sg hw⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
