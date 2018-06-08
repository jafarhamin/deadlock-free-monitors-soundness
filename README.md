# deadlock-free-monitors-soundness
Deadlock-Free Monitors: Soundness Proof In Coq

# Contents 

This repository is still in progress and contains soundness proofs for deadlock-free monitors, carried out by [Coq proof assistant](https://coq.inria.fr) version 8.6.

* Util_Z.v : Basic lemma related to Integers
* Util_list.v : Basic lemma related to lists
* Wait4Graph.v : Lemma proving a valid graph is not deadlock
* Programs.v : Definition of a simpl programming language, its semantics, and the semantics of abort
* Assertions.v : Definition of heaps, assertions, satisfaction relation and some related lemmas
* WeakestPreconditions.v : Definition of the weakest precondition of a command and some related lemmas
* ValidityOfConfigurations.v : Definition of the validity of configurations and some lemmas proving that the small step preseves it
* ProofRules.v : Definitions and proofs of the presented proof rules
* Soundness.v : Soundness proof of the proof rules, i.e. if a program is verified by the proposed proof rules, where the verification starts from an empty bag of obligations and also ends with such bag, this program is deadlock-free

# Some Applications

Some deadlock-free programs verified in [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast/) using the presented proof rules can be found in this repository (in the Applications folder) or at [VeriFast GitHub repository](https://github.com/verifast/verifast)

# The Approach in details

For more details about the presented approach, please look at the following paper:

* [Deadlock-Free Monitors.](https://)

# Contact

* [Jafar Hamin](https://distrinet.cs.kuleuven.be/people/jafar), imec-Distrinet reseach group, KU Leuven, Belgium
* [Bart Jacobs](https://distrinet.cs.kuleuven.be/people/bartj), imec-Distrinet reseach group, KU Leuven, Belgium
