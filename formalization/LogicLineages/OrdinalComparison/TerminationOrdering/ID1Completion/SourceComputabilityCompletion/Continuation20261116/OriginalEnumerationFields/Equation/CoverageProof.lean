module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.ZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.CoverageProof
open OriginalDecodedExchangeEquation
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open OriginalEnumerationFields.CacheCoherence.SideProof
open AgreementDefinitions AgreementSyntaxProof AgreementBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

theorem positive {node param : OTerm alpha}
    (s : Side n body Delta node param)
    (pred old next deps : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (eqn s.index (suc pred))))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph
      OriginalEnumerationFields.rank OriginalEnumerationFields.dependency
      (OriginalEnumerationFields.layer n)) old s.index s.seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList
      OriginalEnumerationFields.dependency) next (suc s.depth) s.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param))) :
    Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  apply agreementIntro (OriginalEnumerationFields.extract n)
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let C : List (Formula (alpha ⊕ Fin 2)) := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (deps.relabel j) key
  let L := graph2 (OriginalEnumerationFields.extract n) value key (param.relabel j)
  let Theta := L :: M :: C
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  let sn := s.rename j Theta hj
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  simp only [eqnRelabel,sucRelabel] at hij
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph3Rename,sucRelabel] at hfj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hm : Nonempty (Derivation body Theta M) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hl : Nonempty (Derivation body Theta L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := (ChildProof.atPrevious sn (pred.relabel j) (old.relabel j) (next.relabel j)
    (deps.relabel j) key value hij hoj hfj hdj hm).mp hl
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction hout)⟩

theorem zero (node param rank old deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param)))
    (hz : Nonempty (Derivation body Delta (eqn rank z))) :
    Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  apply agreementIntro (OriginalEnumerationFields.extract n)
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let C : List (Formula (alpha ⊕ Fin 2)) := Delta.map (fun q => q.relabel j)
  let M := graph2 contains (numeral 1) (deps.relabel j) key
  let L := graph2 (OriginalEnumerationFields.extract n) value key (param.relabel j)
  let Theta := L :: M :: C
  have hj : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hzj := InternalGraphCompositionFunctionalityProof.renameInto hz j Theta hj
  simp only [eqnRelabel,zRelabel] at hzj
  have hm : Nonempty (Derivation body Theta M) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨bad⟩ := ZeroProof.noMember (rank.relabel j) (deps.relabel j) key hrj hdj hm hzj
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.explosion bad))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.CoverageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.CoverageProof
