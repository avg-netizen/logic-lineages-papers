module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherMPBodyProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix DispatcherSupportProof
open DispatcherCombinatorsProof DispatcherPrimitivesProof

theorem entry {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (right : Bool) (q : Program arity)
    (args : List.Vector (Term ctx) arity) (a b : Term ctx)
    (hq : Computes p G q args (.succ (HistoryKernel.pairCall ptag a b))) :
    Computes p G (entryPart right q) args (HistoryDecoder.StepNormalProof.chosen right a b) := by
  apply unary p G args (HistoryDecoder.decoder right) _ (HistoryKernel.pairCall ptag a b)
  · exact unary p G args HistoryCodec.predecessor q _ _ hq (predecessor p G _)
  · exact decoder p G ptag hp right a b

theorem conjunctionOne {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
    (args : List.Vector (Term ctx) arity) (a b : Program arity)
    (ha : Computes p G a args (.succ .zero)) (hb : Computes p G b args (.succ .zero)) :
    Computes p G (conjunction a b) args (.succ .zero) :=
  choosePositive p G args a (constant arity 0) b .zero (.succ .zero) ha hb

theorem body {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (atag ptag ctag : Nat)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (context phi psi : Term ctx) :
    Computes p G mpBody
      (context ::ᵥ psi ::ᵥ .succ (implicationEntry atag ptag ctag context phi psi) ::ᵥ .succ (antecedentEntry ptag context phi) ::ᵥ nil)
      (.succ .zero) := by
  let args := context ::ᵥ psi ::ᵥ .succ (implicationEntry atag ptag ctag context phi psi) ::ᵥ .succ (antecedentEntry ptag context phi) ::ᵥ nil
  have eca := entry p G ptag hp false (.projection (2 : Fin 4)) args context (implicationRaw atag ctag phi psi) (projection p G args 2)
  have ecb := entry p G ptag hp false (.projection (3 : Fin 4)) args context phi (projection p G args 3)
  have era := entry p G ptag hp true (.projection (2 : Fin 4)) args context (implicationRaw atag ctag phi psi) (projection p G args 2)
  have erb := entry p G ptag hp true (.projection (3 : Fin 4)) args context phi (projection p G args 3)
  have hca := binary p G args equalCode (entryPart false (.projection 2)) (.projection 0) context context (.succ .zero)
    eca (projection p G args 0) (equalDiagonal p G context)
  have hcb := binary p G args equalCode (entryPart false (.projection 3)) (.projection 0) context context (.succ .zero)
    ecb (projection p G args 0) (equalDiagonal p G context)
  have happ := binary p G args HistoryAppend.append (entryPart true (.projection 3)) (.projection 1) phi psi
    (HistoryAppend.appendCall atag phi psi) erb (projection p G args 1) (copies p G HistoryAppend.append atag ha _)
  have himp := binary p G args HistoryCodec.cons (constant 4 7)
    (applyTwo HistoryAppend.append (entryPart true (.projection 3)) (.projection 1)) (Term.numeral 7) (HistoryAppend.appendCall atag phi psi)
    (implicationRaw atag ctag phi psi) (constantValue p G args 7) happ (copies p G HistoryCodec.cons ctag hc _)
  have heq := binary p G args equalCode (entryPart true (.projection 2)) _ (implicationRaw atag ctag phi psi) _ (.succ .zero)
    era himp (equalDiagonal p G _)
  have hchecks := conjunctionOne p G args _ _ hca (conjunctionOne p G args _ _ hcb heq)
  exact choosePositive p G args (.projection 2) (constant 4 0) _ (implicationEntry atag ptag ctag context phi psi) (.succ .zero)
    (projection p G args 2)
    (choosePositive p G args (.projection 3) (constant 4 0) _ (antecedentEntry ptag context phi) (.succ .zero)
      (projection p G args 3) hchecks)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherMPBodyProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherMPBodyProof
