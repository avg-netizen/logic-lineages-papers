module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxTargets
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax.Proof

private theorem numeral_decode (n:Nat):BaseTerm.decode (4*n)=.numeral n:=by
  have hm:(4*n)%4=0:=by omega
  have hd:(4*n)/4=n:=by omega
  rw [BaseTerm.decode,dif_pos hm,hd]
private theorem variable_decode (n:Nat):BaseTerm.decode (4*n+1)=.variable n:=by
  have hm:(4*n+1)%4=1:=by omega
  have hn:(4*n+1)%4≠0:=by omega
  have hd:(4*n+1)/4=n:=by omega
  rw [BaseTerm.decode,dif_neg hn,dif_pos hm,hd]
private theorem add_decode (a b:Nat):BaseTerm.decode (4*Nat.pair a b+2)=
    .add (BaseTerm.decode a) (BaseTerm.decode b):=by
  have hm:(4*Nat.pair a b+2)%4=2:=by omega
  have h0:(4*Nat.pair a b+2)%4≠0:=by omega
  have h1:(4*Nat.pair a b+2)%4≠1:=by omega
  have hd:(4*Nat.pair a b+2)/4=Nat.pair a b:=by omega
  rw [BaseTerm.decode,dif_neg h0,dif_neg h1,dif_pos hm,hd,Nat.unpair_pair]
private theorem phi_decode (a:Nat):BaseTerm.decode (4*a+3)=.phi (BaseTerm.decode a):=by
  have h0:(4*a+3)%4≠0:=by omega
  have h1:(4*a+3)%4≠1:=by omega
  have h2:(4*a+3)%4≠2:=by omega
  have hd:(4*a+3)/4=a:=by omega
  rw [BaseTerm.decode,dif_neg h0,dif_neg h1,dif_neg h2,hd]

theorem baseRoundtrip:Targets.BaseSyntaxRoundtrip:=by
  intro E
  induction E with
  | numeral n=>exact numeral_decode n
  | «variable» i=>exact variable_decode i
  | add E F ihE ihF=>simp only [BaseTerm.encode,add_decode,ihE,ihF]
  | phi E ih=>simp only [BaseTerm.encode,phi_decode,ih]

theorem commonRoundtrip:Targets.CommonSyntaxRoundtrip:=by
  intro n
  induction n with
  | zero=>intro E;exact baseRoundtrip E
  | succ n ih=>
    intro E
    rcases E with ⟨c,atoms⟩
    simp only [encodeCommon,decodeCommon,payload,Encodable.encodek,Option.getD_some,List.map_map]
    apply congrArg (fun xs=>(c,xs))
    calc
      _=atoms.map id:=by
        apply List.map_congr_left
        intro a ha
        exact Prod.ext rfl (ih a.2)
      _=atoms:=List.map_id' atoms

private theorem norm_exact (rho:NONote):
    rawNormCode (rawNoteEncode rho.1)=actualOrdinalNorm rho.1.repr:=by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence rho]

theorem sourceCalibration:Targets.ActualSourceCalibration:=by
  intro Γ
  induction Γ with
  | nil=>
    intro E ν
    change (BaseTerm.decode E.encode).value ν=E.value ν
    rw [baseRoundtrip E]
  | cons rho Γ ih=>
    intro E ν
    rcases E with ⟨c,atoms⟩
    simp only [headCodes,List.map_cons,List.length_cons,encodeCommon,payload,Encodable.encodek,Option.getD_some,
      codedValue,commonValue,List.map_map]
    apply congrArg (fun n=>c+n)
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    change (a.1+1)*CommonHeadSmallFold.closedValueCode (rawNoteEncode rho.1)
      (rawNormCode (rawNoteEncode rho.1)+
        codedValue (headCodes Γ) (encodeCommon Γ.length a.2) ν)
      = (a.1+1)*actualHeadValue rho.1.repr
        (actualOrdinalNorm rho.1.repr+commonValue Γ a.2 ν)
    rw [ih a.2 ν,norm_exact rho,(CommonHeadSmallFold.Proof.closedEvaluation.2 rho _).1]
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax.Proof
