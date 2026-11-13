module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSelectProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryLengthOffset HistoryCodec.ArithmeticSupport
open DispatcherSupportProof DispatcherCombinatorsProof DispatcherPrimitivesProof

theorem internalDispatcher : Targets.InternalDispatcher := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag rtag hi hl ha hp hc hd hdrop hr tag ht ctx context phi psi imp ant tailI tailA index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let line := lineValue ptag context psi (lengthCall ltag ant)
  let history := joinedHistory atag ptag ctag context phi psi tailI tailA
  let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
  let V := Formula.equal (call (validityTag tag v l a x) (line ::ᵥ nil)) (.succ .zero)
  let G := [V,H]
  let args := index ::ᵥ fuel ::ᵥ history ::ᵥ line ::ᵥ nil
  have h : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
  have hv : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
  obtain ⟨hrefs⟩ := ReferenceProof.internalReferences v l a x n p itag ltag atag ptag ctag dtag droptag rtag hi hl ha hp hc hd hdrop hr ctx context phi psi imp ant tailI tailA index fuel
  have href := Hilbert.Local.mp (.base hrefs) h
  have h1 : Hilbert.Local T ctx G (.equal (HistoryLookup.lookupCall rtag (lengthCall ltag ant) history) (.succ (implicationEntry atag ptag ctag context phi psi))) :=
    .mp (.base (.logical (.andLeft _ _))) href
  have h2 : Hilbert.Local T ctx G (.equal (HistoryLookup.lookupCall rtag .zero history) (.succ (antecedentEntry ptag context phi))) :=
    .mp (.base (.logical (.andRight _ _))) href
  have hmp := DispatcherReferenceProof.branch p G atag ptag ctag rtag ha hp hc hr context phi psi history (lengthCall ltag ant) index fuel h1 h2
  have hselected := DispatcherSelectProof.ruleSelected p G ptag hp l a x context psi (lengthCall ltag ant) index fuel history hmp
  let g : Fin 3 → Program 4 := Fin.cases (applyOne v HistoryDispatcher.lineCode)
    (Fin.cases (constant 4 0) (Fin.cases (HistoryDispatcher.ruleDispatcher l a x) Fin.elim0))
  have hw := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 0
  have hvnode : (nodes p)[validityTag tag v l a x]? = some ⟨1,v⟩ :=
    SixSol20261112.Fuel.Equations.functionChild p _ v (fun _ => HistoryDispatcher.lineCode) hw
  have hleaf : Computes p G v (line ::ᵥ nil) (.succ .zero) := by
    intro vtag hvt
    obtain ⟨he⟩ := copies p G v (validityTag tag v l a x) hvnode (line ::ᵥ nil) vtag hvt
    exact ⟨localTrans _ _ _ he hv⟩
  have hvalid := unary p G args v HistoryDispatcher.lineCode line (.succ .zero) (projection p G args 3) hleaf
  have hfull := DispatcherMPBodyProof.conjunctionOne p G args _ _ hvalid hselected
  obtain ⟨hout⟩ := hfull tag ht
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherProof
