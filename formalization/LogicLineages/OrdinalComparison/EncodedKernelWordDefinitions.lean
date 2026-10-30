module
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- One concrete finite-list evaluation step: consume the first inner kernel
and accumulate its actual replacement count. The default head is never used
by the length-bounded run on a nonempty remaining word. -/
noncomputable def encodedKernelWordStep (s : List (Nat × Nat) × (Nat × Nat)) :
    List (Nat × Nat) × (Nat × Nat) :=
  let p := s.1.getD 0 (0,0)
  (s.1.tail, (encodedSuffixKernelValue p.1 p.2 s.2.1,
    s.2.2+encodedSuffixKernelCount p.1 p.2 s.2.1))

noncomputable def encodedKernelWordRun (w : List (Nat × Nat)) (t : Nat) : Nat × Nat :=
  ((encodedKernelWordStep^[w.length]) (w,(t,0))).2

def encodePrincipalKernelWord (w : List (ONote × Nat)) : List (Nat × Nat) :=
  w.map (fun p => (rawNoteEncode p.1,p.2))

end LogicLineages.OrdinalComparison
