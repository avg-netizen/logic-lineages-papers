module
public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchTargets
public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeEffectivityProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CertificateSearchEffectivityProof
open FiniteCode CertificateSearch Primrec

theorem certificateFiniteOperationsPrimitiveRecursive :
    Targets.CertificateFiniteOperationsPrimitiveRecursive := by
  obtain ⟨_, _, _, _, hhost, _, hv, _, _, _, _, hn⟩ :=
    FiniteCodeEffectivityProof.forestFiniteTestsPrimitiveRecursive
  have hf : Primrec familyValidTest :=
    ((Primrec.eq.comp hv (const true)).forall_mem_list).decide
  have hm : Primrec₂ makeCertificate :=
    fst.pair (snd.pair (hhost.comp (nat_add.comp (fst.comp fst) (fst.comp snd))))
  have hvf : Primrec₂ verify :=
    Primrec.and.comp (Primrec.and.comp (hf.comp fst)
      ((Primrec.eq.comp (snd.comp (snd.comp snd))
        (hhost.comp (nat_add.comp (fst.comp (fst.comp snd))
          (fst.comp (fst.comp (snd.comp snd)))))).decide))
      (hn.comp (fst.pair ((fst.comp snd).pair (fst.comp (snd.comp snd)))))
  have hi : Primrec₂ atIndex := by
    apply Primrec.ite (Primrec.eq.comp (hf.comp fst) (const true)) _ (const none)
    apply Primrec.option_bind (Primrec.decode.comp snd)
    apply Primrec.ite
      (Primrec.eq.comp (hn.comp ((fst.comp fst).pair ((fst.comp snd).pair (snd.comp snd)))) (const true))
    · exact Primrec.option_some.comp (hm.comp (fst.comp snd) (snd.comp snd))
    · exact const none
  exact ⟨hf, hm, hvf, hi⟩

theorem certificateSearchPartialRecursive : Targets.CertificateSearchPartialRecursive :=
  Partrec.rfindOpt certificateFiniteOperationsPrimitiveRecursive.2.2.2.to_comp

end LogicLineages.ModelsAlgebra.Forests.CertificateSearchEffectivityProof
