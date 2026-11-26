module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.RecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open Continuation20261115.OriginalTypeListsMembership.Targets (allMembers)
open Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof (membersRename)
open SyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consForward (raw head tail allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hg : Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed))) :
    Nonempty (Derivation body Delta (allMembers raw allowed)) := by
  have hparts := RecursionProof.consForward raw head tail allowed hc hg
  have hi := atRawApply tail allowed (belowRawAt raw tail ih (InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc))
  obtain ⟨hf⟩ := andLeft hi
  obtain ⟨ht⟩ := andRight hparts
  have hmem := Nonempty.intro (Derivation.implicationElimination hf ht)
  exact Continuation20261115.OriginalTypeListsMembership.MemberProof.consMembers raw head tail allowed hc (andLeft hparts) hmem

theorem consBackward (raw head tail allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (allMembers raw allowed))) :
    Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed)) := by
  have ht := Continuation20261115.OriginalTypeListsMembership.MemberProof.tailMembers raw head tail allowed hc hm
  have hh := Continuation20261115.OriginalTypeListsMembership.MemberProof.headMember raw head tail allowed hc hm
  have hi := atRawApply tail allowed (belowRawAt raw tail ih (InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc))
  obtain ⟨hb⟩ := andRight hi
  obtain ⟨ht⟩ := ht
  exact RecursionProof.consBackward raw head tail allowed hc hh ⟨Derivation.implicationElimination hb ht⟩

theorem nonzeroForward (raw allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hf : Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed))) :
    Nonempty (Derivation body Delta (allMembers raw allowed)) := by
  apply Boolean.ListCasesProof.nonzeroCases raw _ hn
  intro beta j Theta head tail hj hc
  simp only [membersRename,graph2Rename,sucRelabel,zRelabel]
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hfj := renameInto hf j Theta hj
  simp only [membersRename,graph2Rename,sucRelabel,zRelabel] at hfj
  exact consForward (raw.relabel j) head tail (allowed.relabel j) ihj hc hfj

theorem coreForward (raw allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hf : Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed))) :
    Nonempty (Derivation body Delta (allMembers raw allowed)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := hz
    exact Continuation20261115.OriginalTypeListsMembership.ArithmeticProof.membersTransport z raw allowed ⟨symm hz⟩
      (Continuation20261115.OriginalTypeListsMembership.MemberProof.nilMembers allowed)
  · exact nonzeroForward raw allowed (withHyp ih A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf A.not)

theorem nonzeroBackward (raw allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hf : Nonempty (Derivation body Delta (allMembers raw allowed))) :
    Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed)) := by
  apply Boolean.ListCasesProof.nonzeroCases raw _ hn
  intro beta j Theta head tail hj hc
  simp only [membersRename,graph2Rename,sucRelabel,zRelabel]
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hfj := renameInto hf j Theta hj
  simp only [membersRename,graph2Rename,sucRelabel,zRelabel] at hfj
  exact consBackward (raw.relabel j) head tail (allowed.relabel j) ihj hc hfj

theorem coreBackward (raw allowed : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hf : Nonempty (Derivation body Delta (allMembers raw allowed))) :
    Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := hz
    exact headTransport allTypes (suc z) z raw (Fin.cons allowed Fin.elim0) ⟨symm hz⟩ (RecursionProof.nilValue allowed)
  · exact nonzeroBackward raw allowed (withHyp ih A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.CoreProof
