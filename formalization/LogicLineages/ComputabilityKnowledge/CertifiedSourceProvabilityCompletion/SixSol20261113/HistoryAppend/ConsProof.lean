module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph TableEquationsProof AppendEquationsProof ValueEquationsProof PositiveProof

theorem internalAppendCons : Targets.InternalAppendCons := by
  intro n p tag ctag ht hc ctx a left right
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  let value := call cp (a ::ᵥ left ::ᵥ nil)
  have hv := valueInstalled p (tableTag tag) (tableInstalled p tag ht)
  obtain ⟨hvc,hh,htail,hd,hl,hp⟩ := valueNodes p (valueAt tag) hv
  obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a left
  obtain ⟨hpositive⟩ := appendPositive p tag ht value right
  have hstart := binaryCongruence tag _ _ right right hcons (.logical (.reflexive right))
  obtain ⟨hhead⟩ := HistoryLookup.DestructorProof.internalHeadCons n p (inputHeadTag tag) ctag hh hc ctx a left
  obtain ⟨htailValue⟩ := HistoryLookup.DestructorProof.internalTailCons n p (inputTailTag tag) ctag htail hc ctx a left
  have hhvalue := Logic.trans _ _ _
    (HistoryLookup.DestructorProof.unaryCallCongruence (inputHeadTag tag) _ _ (Support.equalitySymmetry _ _ hcons)) hhead
  have htvalue := Logic.trans _ _ _
    (HistoryLookup.DestructorProof.unaryCallCongruence (inputTailTag tag) _ _ (Support.equalitySymmetry _ _ hcons)) htailValue
  have hrecursive := binaryCongruence tag _ _ right right htvalue (.logical (.reflexive right))
  have hout := binaryCongruence (outputConsTag tag) _ a _ (appendCall tag left right) hhvalue hrecursive
  obtain ⟨hcopy⟩ := consCopies p (outputConsTag tag) ctag hvc hc a (appendCall tag left right)
  exact ⟨Logic.trans _ _ _ hstart (Logic.trans _ _ _ hpositive (Logic.trans _ _ _ hout hcopy))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.ConsProof
