module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplication InternalApplicationSyntaxProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalEqualityTestProof InternalEqualityTestCompositionProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem firstFiveValue (p : Program 5) (value out : OTerm α) (xs : Fin 5 → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma (programGraph (firstFive p) value (inputs xs out))) := by
  apply compositionValue p (fun i => .projection i.castSucc) value (inputs xs out) xs hp
  intro i
  have h := projectionValue (body := body) (Gamma := Gamma) i.castSucc (inputs xs out)
  have he := congrFun (inputsFirst xs out) i
  simpa only [he] using h

theorem resultCheckAccept (result : Program 5) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (hr : Nonempty (Derivation body Gamma (programGraph result out xs))) :
    Nonempty (Derivation body Gamma (programGraph (resultCheck result) (suc z) (inputs xs out))) := by
  apply compositionValue InternalEqualityTest.equalityTest ![.projection 5,firstFive result]
    (suc z) (inputs xs out) ![out,out] (equalityOfEqual out out ⟨refl out⟩)
  intro i
  exact Fin.cases (projectionValue 5 (inputs xs out))
    (Fin.cases (firstFiveValue result out out xs hr) (fun q => Fin.elim0 q)) i

/-- The total builder supplies its output through original existential elimination.
The equality checker is inverted internally, never by semantic calibration. -/
theorem resultCheckRecover (result : Program 5) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (hr : Nonempty (Derivation body Gamma (programGraph (resultCheck result) (suc z) (inputs xs out)))) :
    Nonempty (Derivation body Gamma (programGraph result out xs)) := by
  apply programCases result xs _
  intro β j Delta value hj hv
  simp only [programRename]
  have hr' := renameInto hr j Delta hj
  simp only [programRename,sucRelabel,zRelabel,inputsRename] at hr'
  have he := compositionRecover InternalEqualityTest.equalityTest ![.projection 5,firstFive result]
    (suc z) (inputs (fun i => (xs i).relabel j) (out.relabel j)) ![out.relabel j,value] hr'
    (fun i => Fin.cases (projectionValue 5 (inputs (fun i => (xs i).relabel j) (out.relabel j)))
      (Fin.cases (firstFiveValue result value (out.relabel j) _ hv) (fun q => Fin.elim0 q)) i)
  obtain ⟨heq⟩ := equalityOfAcceptance (out.relabel j) value he
  exact outputTransport result value (out.relabel j) (fun i => (xs i).relabel j) ⟨symm heq⟩ hv

theorem activeAccept (active result : Program 5) (old : Program 6)
    (xs : Fin 5 → OTerm α) (out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph active (suc z) xs)))
    (hr : Nonempty (Derivation body Gamma (programGraph result out xs))) :
    Nonempty (Derivation body Gamma
      (programGraph (application active result old) (suc z) (inputs xs out))) :=
  successorBranchIntro (firstFive active) old (resultCheck result) (suc z) z (inputs xs out)
    (firstFiveValue active (suc z) out xs hc) (resultCheckAccept result xs out hr)

theorem activeRecover (active result : Program 5) (old : Program 6)
    (xs : Fin 5 → OTerm α) (out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph active (suc z) xs)))
    (hr : Nonempty (Derivation body Gamma
      (programGraph (application active result old) (suc z) (inputs xs out)))) :
    Nonempty (Derivation body Gamma (programGraph result out xs)) :=
  resultCheckRecover result xs out
    (successorBranchElim (firstFive active) old (resultCheck result) (suc z) z (inputs xs out)
      (firstFiveValue active (suc z) out xs hc) hr)

theorem actualOriginalActiveGraph : InternalApplicationTargets.ActualOriginalActiveGraph := by
  intro body active result old α xs out
  let c := programGraph active (suc z) xs
  let g := programGraph (application active result old) (suc z) (inputs xs out)
  let s := programGraph result out xs
  obtain ⟨hf⟩ := activeRecover (body := body) (Gamma := [g,c]) active result old xs out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := activeAccept (body := body) (Gamma := [s,c]) active result old xs out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalInactiveGraph : InternalApplicationTargets.ActualOriginalInactiveGraph := by
  intro body active result old α xs out value
  let c := programGraph active z xs
  let g := programGraph (application active result old) value (inputs xs out)
  let s := programGraph old value (inputs xs out)
  obtain ⟨hf⟩ := zeroBranchElim (body := body) (Gamma := [g,c])
    (firstFive active) old (resultCheck result) value (inputs xs out)
    (firstFiveValue active z out xs
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := zeroBranchIntro (body := body) (Gamma := [s,c])
    (firstFive active) old (resultCheck result) value (inputs xs out)
    (firstFiveValue active z out xs
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationGraphProof
