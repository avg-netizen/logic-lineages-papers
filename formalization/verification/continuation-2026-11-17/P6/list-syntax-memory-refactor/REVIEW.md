# Independent list syntax refactor review

Approved for coordinator native. Independently verified archived original SHA1b60b20a76402fb484cb866e89e6684e19ef057545778feec4bbfa5e22a78116 and both proposed current pins. All three original theorem headers and complete allRename proof are byte-identical. Actual source diff adds helper import and changes allSubst/matrixWitness proof implementations only.

Generic matrix is precisely one bound raw variable, actual graph2(member,1,lifted list,raw) and BOTH directions membership↔opaque Meaning. allSubst/witness use ordinary syntax lemmas and explicit Meaning substitution equality, not proof of Meaning or successful membership. Callers instantiate unchanged actual contains and actual Meaning.holds. meaningSubst then six liftSubst/witnessLift rewrites handle bound/fuel/types/heads/labels/tupleBound while the bound raw variable substitutes correctly. Public statements acquire no premise; no original Lists.matrix/Characterizes/AST/targets or caps changed.

Helper is standard opaque proof factoring, no axioms/unsafe/reflection. Native must validate exact definitional specialization and rewrite completion. Memory benefit is not assumed; old failure retained. No reviewer compiler run or full original endpoint claim.
