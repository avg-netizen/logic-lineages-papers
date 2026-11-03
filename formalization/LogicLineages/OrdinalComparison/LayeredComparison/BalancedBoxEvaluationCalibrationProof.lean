module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxClosureProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationTargets
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldEvaluationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof
open BalancedSyntax BalancedEvaluation BalancedEvaluation.Proof

theorem getDOfFn {A:Type} {k:Nat} (f:Fin k→A) (d:A) (j:Nat) (hj:j<k):
    (List.ofFn f).getD j d=f ⟨j,hj⟩:=by
  rw [List.getD_eq_getElem _ d (by simpa using hj)]
  simp only [List.getElem_ofFn]

theorem mapRange_fin {A:Type} (k:Nat) (f:Nat→A) (g:Fin k→A)
    (h:∀j (hj:j<k),f j=g ⟨j,hj⟩):(List.range k).map f=List.ofFn g:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact h i (by simpa using hi)

private theorem flatMap_flatten {A B:Type} (xs:List A) (f:A→List B):
    xs.flatMap f=(xs.map f).flatten:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [List.flatMap_cons,List.map_cons,List.flatten_cons,ih]

theorem flatMapRange_fin {A:Type} (k:Nat) (f:Nat→List A) (g:Fin k→List A)
    (h:∀j (hj:j<k),f j=g ⟨j,hj⟩):
    (List.range k).flatMap f=(List.finRange k).flatMap g:=by
  rw [flatMap_flatten,flatMap_flatten,mapRange_fin k f g h]
  simp only [List.finRange,List.map_ofFn,Function.comp_def]

private theorem actual_norm (rho:NONote):
    rawNormCode (rawNoteEncode rho.1)=actualOrdinalNorm rho.1.repr:=by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence rho]

theorem sourceAtomInput {k:Nat} (a:Nat×Atom k) (v:Fin k→Nat):
    atomInput k (encodeAtom a) (fun j=>(List.ofFn v).getD j 0)=
      BalancedRow.input (List.ofFn v) (asAtom a.2):=by
  unfold atomInput encodeAtom BalancedRow.input BalancedRow.normOffset asAtom
  dsimp only
  rw [actual_norm,BalancedSyntax.Affine.Proof.affineZipOfFn]
  apply congrArg (fun n=>actualOrdinalNorm a.2.head.1.repr+a.2.offset+n)
  apply congrArg List.sum
  apply mapRange_fin
  intro j hj
  rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]

theorem sourceValueAt {k:Nat} (Γ:List Nat) (E:Upper k) (v:Fin k→Nat):
    valueAt k (upperData (encodeSyntax (k::Γ) E)) (fun j=>(List.ofFn v).getD j 0)=
      E.constant+((List.ofFn E.outside).zipWith (·*·) (List.ofFn v)).sum+
      (E.atoms.map (fun a=>(a.1+1)*actualHeadValue a.2.head.1.repr
        (BalancedRow.input (List.ofFn v) (asAtom a.2)))).sum:=by
  simp only [upperData,encodeSyntax,Encodable.encodek,Option.getD_some,valueAt]
  apply congrArg₂ Nat.add
  · apply congrArg (fun n=>E.constant+n)
    apply congrArg List.sum
    rw [BalancedSyntax.Affine.Proof.affineZipOfFn]
    apply mapRange_fin
    intro j hj
    rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]
  · simp only [List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    change (a.1+1)*CommonHeadSmallFold.closedValueCode (rawNoteEncode a.2.head.1)
      (atomInput k (encodeAtom a) (fun j=>(List.ofFn v).getD j 0))=
      (a.1+1)*actualHeadValue a.2.head.1.repr (BalancedRow.input (List.ofFn v) (asAtom a.2))
    rw [sourceAtomInput,(CommonHeadSmallFold.Proof.closedEvaluation.2 a.2.head _).1]

theorem sourceVariablesAt {k:Nat} (Γ:List Nat) (E:Upper k) (v:Fin k→List Nat):
    variablesAt k (upperData (encodeSyntax (k::Γ) E)) (fun j=>(List.ofFn v).getD j [])=
      (List.finRange k).flatMap (fun j=>if E.outside j=0 then [] else v j)++
      E.atoms.flatMap (fun _=>(List.finRange k).flatMap v):=by
  simp only [upperData,encodeSyntax,Encodable.encodek,Option.getD_some,variablesAt]
  apply congrArg₂ List.append
  · apply flatMapRange_fin
    intro j hj
    rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]
  · simp only [List.flatMap_map,Function.comp_def]
    apply flatMap_congr
    intro a ha
    exact flatMapRange_fin k _ v (fun j hj=>getDOfFn v [] j hj)

theorem actualSourceCalibration:Targets.ActualSourceCalibration:=by
  intro Γ
  induction Γ with
  | nil=>
    intro C E table
    change ((CommonLayerSyntax.BaseTerm.decode E.encode).value (BaseTermPrograms.valuation table)=
      E.value (BaseTermPrograms.valuation table))∧
      (CommonLayerSyntax.BaseTerm.decode E.encode).variables=E.variables
    rw [CommonLayerSyntax.Proof.baseRoundtrip E]
    exact ⟨rfl,rfl⟩
  | cons k Γ ih=>
    intro C E table
    let v:Fin k→Nat:=fun j=>value Γ C.1 (C.2 j) (BaseTermPrograms.valuation table)
    let w:Fin k→List Nat:=fun j=>rawVariables Γ C.1 (C.2 j)
    simp only [codeValue,codeVariables,encodeCertificate,certificateData,Encodable.encodek,Option.getD_some]
    have hv:∀j<k,codeValue Γ (encodeCertificate Γ C.1)
        ((List.ofFn (fun i:Fin k=>encodeSyntax Γ (C.2 i))).getD j 0) table=
        (List.ofFn v).getD j 0:=by
      intro j hj
      rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]
      exact (ih C.1 (C.2 ⟨j,hj⟩) table).1
    have hw:∀j<k,codeVariables Γ (encodeCertificate Γ C.1)
        ((List.ofFn (fun i:Fin k=>encodeSyntax Γ (C.2 i))).getD j 0)=
        (List.ofFn w).getD j []:=by
      intro j hj
      rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]
      exact (ih C.1 (C.2 ⟨j,hj⟩) table).2
    rw [valueAt_ext k _ _ _ hv,variablesAt_ext k _ _ _ hw,
      sourceValueAt Γ E v,sourceVariablesAt Γ E w]
    exact ⟨rfl,rfl⟩
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof
