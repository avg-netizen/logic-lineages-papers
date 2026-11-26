module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCases
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralSyntaxStep LiteralSyntaxStep.StepSupportProof
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem expandInstalled {n : Nat} (p : Program n) (stag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) :
 ∃ etag : Nat, (nodes p)[etag]? = some ⟨2,expandCode⟩ := by
 let inner := choose expanded (constant 2 0) (success appended)
 let middle := choose stack (constant 2 0) inner
 let g1 : Fin 3 → Program 2 := Fin.cases (.projection 0) (Fin.cases (constant 2 0) (Fin.cases middle Fin.elim0))
 let t1 := stag+argumentTag HistoryCodec.select g1 2
 have h1 := Equations.argumentChild p stag HistoryCodec.select g1 hs 2
 let g2 : Fin 3 → Program 2 := Fin.cases stack (Fin.cases (constant 2 0) (Fin.cases inner Fin.elim0))
 let t2 := t1+argumentTag HistoryCodec.select g2 2
 have h2 := Equations.argumentChild p t1 HistoryCodec.select g2 h1 2
 let g3 : Fin 3 → Program 2 := Fin.cases expanded (Fin.cases (constant 2 0) (Fin.cases (success appended) Fin.elim0))
 let t3 := t2+argumentTag HistoryCodec.select g3 0
 have h3 := Equations.argumentChild p t2 HistoryCodec.select g3 h2 0
 exact ⟨t3+1,Equations.functionChild p t3 expandCode (Fin.cases headTask (Fin.cases (.projection 1) Fin.elim0)) h3⟩

theorem rejectedCons {n ctx : Nat} (p : Program n) (stag etag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (t rest token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (expandCall etag t token) .zero)
    (.equal (stepCall stag (.succ (HistoryLookup.consCall ctag t rest)) token) .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := Formula.equal (expandCall etag t token) .zero
 let G := [A]
 let row := HistoryLookup.consCall ctag t rest
 let args := (.succ row ::ᵥ token ::ᵥ nil)
 have hstack : Computes p G stack args row :=
  unary p G args HistoryCodec.predecessor (.projection 0) (.succ row) row
    (projection p G args 0) (predecessor p G row)
 have hhead : Computes p G headTask args t :=
  unary p G args HistoryLookup.head stack row t hstack (headCons p G ctag hc t rest)
 have hexpand : Computes p G expanded args .zero := by
  apply binary p G args expandCode headTask (.projection 1) t token .zero hhead (projection p G args 1)
  exact changeValue p G expandCode (t ::ᵥ token ::ᵥ nil) (expandCall etag t token) .zero
    (copies p G expandCode etag he _) (.hypothesis List.mem_cons_self)
 let pairTag := ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pairValue := call pairTag (t ::ᵥ rest ::ᵥ nil)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx t rest
 have hpositive : Computes p G stack args (.succ pairValue) := changeValue p G stack args row _ hstack (.base hcons)
 have h : Computes p G stepCode args .zero :=
  choosePositive p G args (.projection 0) (constant 2 0) _ row _ (projection p G args 0)
   (choosePositive p G args stack (constant 2 0) _ pairValue _ hpositive
    (chooseZero p G args expanded (constant 2 0) _ .zero hexpand (constantValue p G args 0)))
 obtain ⟨hout⟩ := h stag hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCases
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCases
