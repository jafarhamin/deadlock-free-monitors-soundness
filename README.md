# deadlock-free-monitors-soundness
Deadlock-Free Monitors: A Soundness Proof in Coq

This repository contains a soundness proof, carried out by [Coq proof assistant v8.6](https://coq.inria.fr), for deadlock-free monitors, a modular approach to verify deadlock-freedom of programs synchronized by condition variables.

An HTML representation of this proof can be found [here](https://www.hamin.be/dfm/html/dfm.html).

For more details about the approach please look at:
* [The Deadlock-Free Monitors Paper](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_15), published in [27th European Symposium on Programming, ESOP 2018](https://link.springer.com/book/10.1007/978-3-319-89884-1)
* [The extended version of this paper](https://lirias2repo.kuleuven.be/bitstream/id/500138/), published as a technical report in [Department of Computer Science, KU Leuven](https://wms.cs.kuleuven.be/cs/english)
* [Some deadlock-free programs](https://github.com/verifast/verifast/tree/master/examples/monitors), verified in [VeriFast](https://people.cs.kuleuven.be/~bart.jacobs/verifast/), using the proposed proof rules

This project has received funding from [the European Union’s Horizon 2020 research and innovation programme](https://ec.europa.eu/programmes/horizon2020/en) under grant agreement No 731453 ([VESSEDIA](https://vessedia.eu/)).

# Contents 

* Util_Z.v : Some basic lemmas related to Integers
* Util_list.v : Some basic lemmas related to lists
* RelaxedPrecedenceRelation.v : A lemma proving that a valid graph is deadlock-free
* Programs.v : Definitions of a simple programming language, and its semantics
* Assertions.v : Definitions of heaps, assertions, and satisfaction relation along with some related lemmas
* WeakestPreconditions.v : The definition of the weakest precondition of a command along with some related lemmas
* ValidityOfConfigurations.v : The definition of the validity of configurations along with some lemmas proving that the small step preseves it
* ProofRules.v : The proposed proof rules
* Soundness.v : The soundness proof of the proposed proof rules, i.e. any program that is verified by the proposed proof rules is deadlock-free
* html : An HTML representation of the proof scripts
# Contact

* [Jafar Hamin](https://distrinet.cs.kuleuven.be/people/jafar), imec-Distrinet reseach group, KU Leuven, Belgium
* [Bart Jacobs](https://distrinet.cs.kuleuven.be/people/bartj), imec-Distrinet reseach group, KU Leuven, Belgium
