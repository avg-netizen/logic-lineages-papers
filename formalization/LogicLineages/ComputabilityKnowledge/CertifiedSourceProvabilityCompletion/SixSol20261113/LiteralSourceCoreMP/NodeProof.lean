module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.NodeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries HistoryRuleSuffix

theorem lengthInstalled {n : Nat} (p : Program n) (stag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩) :
 (nodes p)[lengthTag stag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ := by
 let outer : Fin 1 → Program 2 := fun _ => LiteralSyntaxScan.finalState
 have hf := Fuel.Equations.argumentChild p stag (HistoryDecoder.decoder true) outer hs 0
 let ftag := stag + argumentTag (HistoryDecoder.decoder true) outer 0
 let fs : Fin 2 → Program 2 := Fin.cases
  (applyOne HistoryLengthOffset.lengthProgram (.projection 1))
  (Fin.cases LiteralSyntaxScan.initial Fin.elim0)
 have hlw := Fuel.Equations.argumentChild p ftag LiteralSyntaxScan.iterator fs hf 0
 exact Fuel.Equations.functionChild p (ftag + argumentTag LiteralSyntaxScan.iterator fs 0)
   HistoryLengthOffset.lengthProgram (fun _ : Fin 1 => .projection (1 : Fin 2)) hlw

theorem appendLookupDrop {n : Nat} (p : Program n) (atag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) :
 (nodes p)[lookupTag atag]? = some ⟨2,HistoryLookup.lookup⟩ ∧
 (nodes p)[dropTag atag]? = some ⟨2,HistoryLookup.drop⟩ := by
 have ht := HistoryAppend.AppendEquationsProof.tableInstalled p atag ha
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p
   (HistoryAppend.AppendEquationsProof.tableTag atag) ht
 obtain ⟨_,_,_,_,hr,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p
   (HistoryAppend.TableEquationsProof.valueTag (HistoryAppend.AppendEquationsProof.tableTag atag)) hv
 have hd := Fuel.Equations.argumentChild p (lookupTag atag) HistoryLookup.reference
   (fun _ : Fin 1 => HistoryLookup.drop) hr 0
 exact ⟨hr,hd⟩

theorem dispatcherInstalled {n : Nat} (p : Program n) (ktag : Nat)
 (l a : Program 1) (x : Program 3)
 (hk : (nodes p)[ktag]? = some ⟨3,HistoryKernel.kernel valid l a x⟩) :
 (nodes p)[HistoryKernel.TransitionEquationsProof.dispatcherTag ktag valid l a x]? =
   some ⟨4,HistoryDispatcher.lineDispatcher valid l a x⟩ := by
 have h := HistoryKernel.TransitionEquationsProof.checkInstalled p ktag valid l a x hk
 exact Fuel.Equations.functionChild p
   (HistoryKernel.TransitionEquationsProof.checkTag ktag valid l a x)
   (HistoryDispatcher.lineDispatcher valid l a x) HistoryKernel.dispatcherArguments h

theorem coreInstalled (pF pR l a : Program 1) (x : Program 3) :
 let q := LiteralKernelSource.verifier valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 (nodes root)[coreTag pF l a x]? =
   some ⟨5,LiteralKernelSource.coreChecker valid l a x bound initial finalizer⟩ := by
 let q0 := LiteralKernelSource.coreChecker valid l a x bound initial finalizer
 let q := LiteralKernelSource.verifier valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 have ht : (nodes root)[GorbowNamedInternalProvability.checkerTag pF]? = some ⟨5,Fuel.verifier q0⟩ :=
   GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 exact LiteralCheckerAuxiliaries.InstallationProof.coreInstalled root
   (GorbowNamedInternalProvability.checkerTag pF) q0 ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.NodeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.NodeProof
