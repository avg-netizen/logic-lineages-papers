module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherMPBodyProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherReferenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport DispatcherSupportProof
open DispatcherCombinatorsProof DispatcherPrimitivesProof

theorem lookupKnown {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) rtag
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩) (index history entry : Term ctx)
    (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (HistoryLookup.lookupCall rtag index history) (.succ entry))) :
    Computes p G HistoryLookup.lookup (index ::ᵥ history ::ᵥ nil) (.succ entry) := by
  intro tag ht
  obtain ⟨he⟩ := copies p G HistoryLookup.lookup rtag hr (index ::ᵥ history ::ᵥ nil) tag ht
  exact ⟨localTrans _ _ _ he h⟩

theorem check {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (atag ptag ctag rtag : Nat)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩) (context phi psi history ref1 : Term ctx)
    (h1 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (HistoryLookup.lookupCall rtag ref1 history) (.succ (implicationEntry atag ptag ctag context phi psi))))
    (h2 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (HistoryLookup.lookupCall rtag .zero history) (.succ (antecedentEntry ptag context phi)))) :
    Computes p G mpCheck (history ::ᵥ context ::ᵥ psi ::ᵥ ref1 ::ᵥ .zero ::ᵥ nil) (.succ .zero) := by
  let args := history ::ᵥ context ::ᵥ psi ::ᵥ ref1 ::ᵥ .zero ::ᵥ nil
  let values := context ::ᵥ psi ::ᵥ .succ (implicationEntry atag ptag ctag context phi psi) ::ᵥ .succ (antecedentEntry ptag context phi) ::ᵥ nil
  apply compose p G mpBody mpArguments args values (.succ .zero) _ (DispatcherMPBodyProof.body p G atag ptag ctag ha hp hc context phi psi)
  intro i
  cases i using Fin.cases with
  | zero => exact projection p G args 1
  | succ i => cases i using Fin.cases with
    | zero => exact projection p G args 2
    | succ i => cases i using Fin.cases with
      | zero =>
        exact binary p G args HistoryLookup.lookup (.projection 3) (.projection 0) ref1 history _
          (projection p G args 3) (projection p G args 0) (lookupKnown p G rtag hr ref1 history _ h1)
      | succ i => cases i using Fin.cases with
        | zero =>
          exact binary p G args HistoryLookup.lookup (.projection 4) (.projection 0) .zero history _
            (projection p G args 4) (projection p G args 0) (lookupKnown p G rtag hr .zero history _ h2)
        | succ i => exact Fin.elim0 i

theorem branch {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (atag ptag ctag rtag : Nat)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩) (context phi psi history ref1 index fuel : Term ctx)
    (h1 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (HistoryLookup.lookupCall rtag ref1 history) (.succ (implicationEntry atag ptag ctag context phi psi))))
    (h2 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
      (.equal (HistoryLookup.lookupCall rtag .zero history) (.succ (antecedentEntry ptag context phi)))) :
    Computes p G HistoryDispatcher.mpBranch
      (index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context psi ref1 ::ᵥ nil) (.succ .zero) := by
  let args := index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context psi ref1 ::ᵥ nil
  obtain ⟨hcontext,hraw,hrule,htag,hargs,href1,href2⟩ := DispatcherFieldsProof.fields p G ptag hp context psi ref1 index fuel history
  have hg1 := binary p G args equalCode HistoryDispatcher.payloadTag (constant 4 0) .zero .zero (.succ .zero)
    htag (constantValue p G args 0) (equalDiagonal p G .zero)
  have hg2 := binary p G args equalCode HistoryDispatcher.payloadArgs (constant 4 0) .zero .zero (.succ .zero)
    hargs (constantValue p G args 0) (equalDiagonal p G .zero)
  have hguard := DispatcherMPBodyProof.conjunctionOne p G args _ _ hg1 hg2
  have hm : Computes p G (.composition mpCheck HistoryDispatcher.mpArguments) args (.succ .zero) := by
    apply compose p G mpCheck HistoryDispatcher.mpArguments args
      (history ::ᵥ context ::ᵥ psi ::ᵥ ref1 ::ᵥ .zero ::ᵥ nil) (.succ .zero) _
      (check p G atag ptag ctag rtag ha hp hc hr context phi psi history ref1 h1 h2)
    intro i
    cases i using Fin.cases with
    | zero => exact projection p G args 2
    | succ i => cases i using Fin.cases with
      | zero => exact hcontext
      | succ i => cases i using Fin.cases with
        | zero => exact hraw
        | succ i => cases i using Fin.cases with
          | zero => exact href1
          | succ i => cases i using Fin.cases with
            | zero => exact href2
            | succ i => exact Fin.elim0 i
  exact DispatcherMPBodyProof.conjunctionOne p G args _ _ hguard hm
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherReferenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherReferenceProof
